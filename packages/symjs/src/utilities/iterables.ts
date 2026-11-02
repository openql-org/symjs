// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of SymPy's `sympy.utilities.iterables`.
 *
 * Python conventions are mapped as follows: tuples and lists are arrays,
 * dicts are {@link ValueMap}s (a `Map` whose keys compare by value), sets are
 * `Set`s and generators are generator functions yielding in SymPy's order.
 * Strings are accepted wherever SymPy iterates over the characters of a
 * string. Values compare like Python's `==` (expressions structurally,
 * arrays element by element) and order like Python's `<`.
 *
 * Generators that SymPy documents as reusing one list in place
 * (`ordered_partitions`, `binary_partitions`, `multiset_derangements`) yield
 * a fresh array each time in symjs, so collecting their output gives the
 * partitions themselves instead of copies of the last state.
 */

import type { Assumptions } from '../core/nodes';
import { Expr, Sym, isNum } from '../core/nodes';
import { neg } from '../core/ops';
import { MultisetPartitionTraverser, listVisitor, multisetPartitionsTaocp } from './enumerative';
import { combinations, combinationsWithReplacement, permutations, product } from './itertools';
import { ValueMap, compareValues, orderedValues, valueEquals, valueKey } from './values';
import type { KeyFunction } from './values';

/** A class (or anything usable on the right of `instanceof`) naming a type. */
export type TypeSpec = { [Symbol.hasInstance](value: unknown): boolean };

/** A graph given as its vertices and its directed edges. */
export type Graph<T> = readonly [vertices: readonly T[], edges: readonly (readonly [T, T])[]];

/** A sequence: an array or a string. */
type Sequence<T> = readonly T[] | string;

/** The number at index i (arrays of numbers are dense here). */
const at = (xs: readonly number[], i: number): number => xs[i] as number;

function checkInt(n: number, what: string): number {
  if (!Number.isInteger(n)) throw new TypeError(`${what} must be an integer, got ${n}`);
  return n;
}

// ---------------------------------------------------------------------------
// type tests

/**
 * Mixin marker (SymPy `NotIterable`): instances of classes extending it are
 * not iterable for {@link iterable}.
 */
export class NotIterable {}

/** `x instanceof spec`, with String, Number, Boolean and BigInt also matching primitives. */
function isInstance(x: unknown, spec: TypeSpec): boolean {
  if ((spec as unknown) === String) return typeof x === 'string' || x instanceof String;
  if ((spec as unknown) === Number) return typeof x === 'number' || x instanceof Number;
  if ((spec as unknown) === Boolean) return typeof x === 'boolean' || x instanceof Boolean;
  if ((spec as unknown) === BigInt) return typeof x === 'bigint';
  return x instanceof spec;
}

function isInstanceOfAny(x: unknown, spec: TypeSpec | readonly TypeSpec[]): boolean {
  return Array.isArray(spec) ? (spec as readonly TypeSpec[]).some((s) => isInstance(x, s)) : isInstance(x, spec as TypeSpec);
}

const GeneratorPrototype = Object.getPrototypeOf(Object.getPrototypeOf((function* () {})())) as object;

/**
 * The type of generator objects (Python `types.GeneratorType`), usable as an
 * `include` or `exclude` entry: `isSequence(gen, [String, GeneratorType])`.
 */
export const GeneratorType: TypeSpec = {
  [Symbol.hasInstance](value: unknown): boolean {
    return typeof value === 'object' && value !== null && GeneratorPrototype.isPrototypeOf(value);
  },
};

/**
 * SymPy `iterable(i, exclude=(str, dict, NotIterable))`: whether `i` can be
 * iterated (and the iteration is finite). Strings, `Map`s (Python dicts)
 * and {@link NotIterable} instances are excluded by default; pass `null` to
 * exclude nothing. An `_iterable` property on the object overrides the test.
 */
export function iterable(i: unknown, exclude: TypeSpec | readonly TypeSpec[] | null = [String, Map, NotIterable]): boolean {
  if (typeof i === 'object' && i !== null && '_iterable' in i) return Boolean(i._iterable);
  const canIterate =
    typeof i === 'string' || (typeof i === 'object' && i !== null && typeof (i as { [Symbol.iterator]?: unknown })[Symbol.iterator] === 'function');
  if (!canIterate) return false;
  if (exclude !== null && (!Array.isArray(exclude) || exclude.length > 0)) return !isInstanceOfAny(i, exclude);
  return true;
}

/**
 * SymPy `is_sequence(i, include=None)`: whether `i` is an indexable
 * iterable (an array or a typed array) that {@link iterable} accepts, or an
 * instance of one of the `include` types.
 */
export function isSequence(i: unknown, include?: TypeSpec | readonly TypeSpec[] | null): boolean {
  const indexable = Array.isArray(i) || ArrayBuffer.isView(i) || typeof i === 'string';
  if (indexable && iterable(i)) return true;
  return include !== undefined && include !== null && isInstanceOfAny(i, include);
}

// ---------------------------------------------------------------------------
// simple sequence operations

function sliceIndices(len: number, start: number, stop: number | undefined): [number, number] {
  const norm = (v: number) => (v < 0 ? Math.max(0, v + len) : Math.min(v, len));
  return [norm(start), stop === undefined ? len : norm(stop)];
}

/**
 * SymPy `is_palindromic(s, i=0, j=None)`: whether `s` (or the Python slice
 * `s[i:j]`) reads the same in both directions.
 */
export function isPalindromic<T>(s: Sequence<T>, i = 0, j?: number): boolean {
  const [a, b] = sliceIndices(s.length, i, j);
  const m = Math.floor((b - a) / 2);
  for (let k = 0; k < m; k++) if (!valueEquals(s[a + k], s[b - 1 - k])) return false;
  return true;
}

/**
 * SymPy `flatten(iterable, levels=None, cls=None)`: recursively denest
 * arrays and sets (or, with `cls`, expressions of that class through their
 * arguments), at most `levels` levels deep.
 */
export function flatten(iter: Iterable<unknown>, opts: { levels?: number | null; cls?: TypeSpec | null } = {}): unknown[] {
  let levels = opts.levels ?? null;
  const cls = opts.cls ?? null;
  if (levels !== null) {
    if (levels === 0) return iter as unknown[];
    if (levels > 0) levels -= 1;
    else throw new RangeError(`expected non-negative number of levels, got ${levels}`);
  }
  const reducible = cls === null ? (x: unknown) => isSequence(x, Set) : (x: unknown) => isInstance(x, cls);
  const result: unknown[] = [];
  for (const el of iter) {
    if (reducible(el)) {
      const inner = el instanceof Expr ? el.args : (el as Iterable<unknown>);
      result.push(...flatten(inner, { levels, cls }));
    } else {
      result.push(el);
    }
  }
  return result;
}

/**
 * SymPy `unflatten(iter, n=2)`: group `iter` into tuples of length `n`.
 * Throws a RangeError when the length is not a multiple of `n`.
 */
export function unflatten<T>(iter: readonly T[], n = 2): T[][] {
  if (n < 1 || iter.length % n) throw new RangeError(`iter length is not a multiple of ${n}`);
  const out: T[][] = [];
  for (let i = 0; i < iter.length; i += n) out.push(iter.slice(i, i + n));
  return out;
}

/** A reshape template: counts, nested arrays (lists and tuples) and sets of counts. */
export type ReshapeTemplate = readonly (number | ReshapeTemplate | ReadonlySet<number | ReshapeTemplate>)[] | ReadonlySet<number | ReshapeTemplate>;

function templateSum(how: ReshapeTemplate): number {
  return (flatten(how as Iterable<unknown>) as number[]).reduce((a, b) => a + b, 0);
}

/**
 * SymPy `reshape(seq, how)`: reshape `seq` according to the template
 * `how`, made of counts, arrays and sets. Python distinguishes lists and
 * tuples in the template; both are arrays here.
 */
export function reshape<T>(seq: readonly T[], how: ReshapeTemplate): unknown[] {
  const m = templateSum(how);
  if (m <= 0 || seq.length % m) throw new RangeError('template must sum to positive number that divides the length of the sequence');
  const n = seq.length / m;
  let i = 0;
  const isSet = how instanceof Set;
  const rv: unknown[] = [];
  for (let k = 0; k < n; k++) {
    const part: unknown[] = [];
    for (const hi of how as Iterable<number | ReshapeTemplate>) {
      if (typeof hi === 'number') {
        part.push(...seq.slice(i, i + hi));
        i += hi;
      } else {
        const c = templateSum(hi);
        const inner = reshape(seq.slice(i, i + c), hi)[0] as unknown[] | Set<unknown>;
        part.push(hi instanceof Set ? new Set(inner) : [...inner]);
        i += c;
      }
    }
    rv.push(isSet ? new Set(part) : part);
  }
  return rv;
}

/**
 * SymPy `group(seq, multiple=True)`: split `seq` into lists of equal
 * adjacent elements, or (with `multiple: false`) into `[element, count]`
 * pairs.
 */
export function group<T>(seq: Iterable<T>, opts?: { multiple?: true }): T[][];
export function group<T>(seq: Iterable<T>, opts: { multiple: false }): [T, number][];
export function group<T>(seq: Iterable<T>, opts: { multiple?: boolean } = {}): T[][] | [T, number][] {
  const runs: T[][] = [];
  for (const x of seq) {
    const last = runs[runs.length - 1];
    if (last && valueEquals(last[0], x)) last.push(x);
    else runs.push([x]);
  }
  if (opts.multiple ?? true) return runs;
  return runs.map((r): [T, number] => [r[0] as T, r.length]);
}

const iproduct2 = function* <A, B>(iterable1: Iterable<A>, iterable2: Iterable<B>): Generator<[A, B], void, undefined> {
  const it1 = iterable1[Symbol.iterator]();
  const it2 = iterable2[Symbol.iterator]();
  const elems1: A[] = [];
  const elems2: B[] = [];
  const append = <E>(it: Iterator<E>, elems: E[]) => {
    const r = it.next();
    if (r.done !== true) elems.push(r.value);
  };
  let n = 0;
  append(it1, elems1);
  append(it2, elems2);
  while (n <= elems1.length + elems2.length) {
    for (let m = n - elems1.length + 1; m < elems2.length; m++) yield [elems1[n - m]!, elems2[m]!];
    n++;
    append(it1, elems1);
    append(it2, elems2);
  }
};

/**
 * SymPy `iproduct(*iterables)`: the Cartesian product of possibly infinite
 * iterables; every tuple of the product is reached eventually.
 */
export function* iproduct<T>(...iterables: Iterable<T>[]): Generator<T[], void, undefined> {
  if (iterables.length === 0) {
    yield [];
    return;
  }
  if (iterables.length === 1) {
    for (const e of iterables[0]!) yield [e];
    return;
  }
  if (iterables.length === 2) {
    for (const [a, b] of iproduct2(iterables[0]!, iterables[1]!)) yield [a, b];
    return;
  }
  const [first, ...others] = iterables;
  for (const [ef, eo] of iproduct2(first!, iproduct(...others))) yield [ef, ...eo];
}

/**
 * SymPy `multiset(seq)`: the multiplicity of each element of `seq`, in
 * order of first appearance.
 */
export function multiset<T>(seq: Iterable<T>): ValueMap<T, number> {
  const m = new ValueMap<T, number>();
  for (const x of seq) m.set(x, (m.get(x) ?? 0) + 1);
  return m;
}

function bitString(n: bigint): string {
  return n.toString(2);
}

/**
 * SymPy `ibin(n, bits=None, str=False)`: the binary digits of `n` (most
 * significant first), padded to `bits` digits. With a non-integer `bits`
 * (e.g. `'all'`), a generator of all `n`-digit bit lists (or strings with
 * `str: true`) from all zeros to all ones.
 */
export function ibin(n: number | bigint, bits?: number | null, opts?: { str?: false }): number[];
export function ibin(n: number | bigint, bits: number | null | undefined, opts: { str: true }): string;
export function ibin(n: number | bigint, bits: string, opts?: { str?: false }): Generator<number[], void, undefined>;
export function ibin(n: number | bigint, bits: string, opts: { str: true }): Generator<string, void, undefined>;
export function ibin(
  n: number | bigint,
  bits?: number | string | null,
  opts: { str?: boolean } = {},
): number[] | string | Generator<number[], void, undefined> | Generator<string, void, undefined> {
  if (n < 0) throw new RangeError('negative numbers are not allowed');
  if (typeof n === 'number') checkInt(n, 'n');
  const N = BigInt(n);
  let b: number;
  if (bits === undefined || bits === null) {
    b = 0;
  } else if (typeof bits === 'number' && Number.isInteger(bits)) {
    b = bits;
    if (bitString(N).replace(/^0$/, '').length > b) throw new RangeError(`\`bits\` must be >= ${N === 0n ? 0 : bitString(N).length}`);
  } else {
    b = -1;
  }
  if (opts.str !== true) {
    if (b >= 0) return bitString(N).padStart(b, '0').split('').map((c) => (c === '1' ? 1 : 0));
    return variations([0, 1], Number(N), { repetition: true });
  }
  if (b >= 0) return bitString(N).padStart(b, '0');
  const count = Number(N);
  return (function* () {
    for (let i = 0n; i < 2n ** N; i++) yield bitString(i).padStart(count, '0');
  })();
}

/**
 * SymPy `variations(seq, n, repetition=False)`: the `n`-sized ordered
 * selections of `seq`, without (permutations) or with (Cartesian power)
 * repetition.
 */
export function* variations<T>(seq: Iterable<T>, n: number, opts: { repetition?: boolean } = {}): Generator<T[], void, undefined> {
  const items = [...seq];
  if (opts.repetition !== true) {
    if (items.length < n) return;
    yield* permutations(items, n);
    return;
  }
  if (n === 0) {
    yield [];
    return;
  }
  yield* product(Array.from({ length: n }, () => items));
}

/**
 * SymPy `subsets(seq, k=None, repetition=False)`: the `k`-subsets
 * (combinations) of `seq`, or all subsets from shortest to longest when `k`
 * is omitted; with `repetition`, combinations with replacement.
 */
export function* subsets<T>(seq: Iterable<T>, k?: number | null, opts: { repetition?: boolean } = {}): Generator<T[], void, undefined> {
  const items = [...seq];
  const comb = opts.repetition === true ? combinationsWithReplacement : combinations;
  if (k === undefined || k === null) {
    for (let r = 0; r <= items.length; r++) yield* comb(items, r);
  } else {
    yield* comb(items, k);
  }
}

/** SymPy `filter_symbols(iterator, exclude)`: the elements of `iterator` not in `exclude`. */
export function* filterSymbols<T>(iterator: Iterable<T>, exclude: Iterable<T>): Generator<T, void, undefined> {
  const ex = new Set<string>();
  for (const e of exclude) ex.add(valueKey(e));
  for (const s of iterator) if (!ex.has(valueKey(s))) yield s;
}

/** A symbol class for {@link numberedSymbols} (`Sym`, `Dummy`, `Wild`, ...). */
export type SymbolClass<S extends Sym> = new (name: string, assumptions?: Assumptions) => S;

/**
 * SymPy `numbered_symbols(prefix='x', cls=None, start=0, exclude=(), **assumptions)`:
 * an infinite stream of symbols `x0, x1, ...` skipping those in `exclude`.
 * The remaining options are assumptions passed to the class.
 */
export function numberedSymbols<S extends Sym = Sym>(
  prefix = 'x',
  opts: { cls?: SymbolClass<S>; start?: number; exclude?: Iterable<Expr> } & Assumptions = {},
): Generator<S, never, undefined> {
  const { cls, start = 0, exclude = [], ...assumptions } = opts;
  const C = cls ?? (Sym as unknown as SymbolClass<S>);
  const ex = new Set<string>();
  for (const e of exclude) ex.add(e.key);
  return (function* (): Generator<S, never, undefined> {
    for (let i = start; ; i++) {
      const s = new C(`${prefix}${i}`, assumptions);
      if (!ex.has(s.key)) yield s;
    }
  })();
}

/** The `print` function handed to the callback of {@link capture}. */
export type PrintFunction = (...values: unknown[]) => void;

/**
 * SymPy `capture(func)`: the text that `func` prints. JavaScript has no
 * standard output to redirect, so `func` receives a `print` function that
 * behaves like Python's (values converted with `String`, separated by a
 * space, followed by a newline) and `capture` returns what was printed.
 */
export function capture(func: (print: PrintFunction) => void): string {
  let out = '';
  func((...values: unknown[]) => {
    out += `${values.map((v) => String(v)).join(' ')}\n`;
  });
  return out;
}

/** A truth-like key for the binary form of {@link sift}. */
type BinaryKey = boolean | number | 'unknown';

/**
 * SymPy `sift(seq, keyfunc, binary=False)`: the elements of `seq` grouped by
 * the value of `keyfunc` (a {@link ValueMap} from key to elements), or with
 * `binary: true` the pair `[elements giving true, elements giving false]`;
 * a key other than true/false (or 1/0) then throws a RangeError.
 */
export function sift<T, K>(seq: Iterable<T>, keyfunc: (x: T) => K, opts?: { binary?: false }): ValueMap<K, T[]>;
export function sift<T>(seq: Iterable<T>, keyfunc: (x: T) => BinaryKey, opts: { binary: true }): [T[], T[]];
export function sift<T, K>(seq: Iterable<T>, keyfunc: (x: T) => K, opts: { binary?: boolean } = {}): ValueMap<K, T[]> | [T[], T[]] {
  if (opts.binary !== true) {
    const m = new ValueMap<K, T[]>();
    for (const x of seq) {
      const k = keyfunc(x);
      const g = m.get(k);
      if (g) g.push(x);
      else m.set(k, [x]);
    }
    return m;
  }
  const T: T[] = [];
  const F: T[] = [];
  for (const x of seq) {
    const k = keyfunc(x) as unknown;
    if (k === true || k === 1) T.push(x);
    else if (k === false || k === 0) F.push(x);
    else throw new RangeError('keyfunc gave non-binary output');
  }
  return [T, F];
}

/** SymPy `take(iter, n)`: the first `n` items of `iter`. */
export function take<T>(iter: Iterable<T>, n: number): T[] {
  const out: T[] = [];
  if (n <= 0) return out;
  for (const x of iter) {
    out.push(x);
    if (out.length >= n) break;
  }
  return out;
}

/** SymPy `dict_merge(*dicts)`: merge maps; later maps override earlier ones. */
export function dictMerge<K, V>(...dicts: ReadonlyMap<K, V>[]): ValueMap<K, V> {
  const merged = new ValueMap<K, V>();
  for (const d of dicts) for (const [k, v] of d) merged.set(k, v);
  return merged;
}

/** SymPy `common_prefix(*seqs)`: the longest common start of the sequences. */
export function commonPrefix<T>(...seqs: readonly (readonly T[])[]): T[] {
  if (seqs.length === 0 || seqs.some((s) => s.length === 0)) return [];
  const first = seqs[0]!;
  if (seqs.length === 1) return [...first];
  const n = Math.min(...seqs.map((s) => s.length));
  let i = 0;
  while (i < n && seqs.every((s) => valueEquals(s[i], first[i]))) i++;
  return first.slice(0, i);
}

/** SymPy `common_suffix(*seqs)`: the longest common ending of the sequences. */
export function commonSuffix<T>(...seqs: readonly (readonly T[])[]): T[] {
  if (seqs.length === 0 || seqs.some((s) => s.length === 0)) return [];
  const first = seqs[0]!;
  if (seqs.length === 1) return [...first];
  const n = Math.min(...seqs.map((s) => s.length));
  let i = 0;
  while (i < n && seqs.every((s) => valueEquals(s[s.length - 1 - i], first[first.length - 1 - i]))) i++;
  return first.slice(first.length - i);
}

/** SymPy `prefixes(seq)`: the prefixes of `seq`, shortest first. */
export function* prefixes<T>(seq: readonly T[]): Generator<T[], void, undefined> {
  for (let i = 0; i < seq.length; i++) yield seq.slice(0, i + 1);
}

/** SymPy `postfixes(seq)`: the suffixes of `seq`, shortest first. */
export function* postfixes<T>(seq: readonly T[]): Generator<T[], void, undefined> {
  const n = seq.length;
  for (let i = 0; i < n; i++) yield seq.slice(n - i - 1);
}

// ---------------------------------------------------------------------------
// graphs

/**
 * SymPy `topological_sort(graph, key=None)`: the vertices of the acyclic
 * graph `[V, E]` in topological order, ties broken by the natural order of
 * `key(v)` (the vertices themselves by default). Throws a RangeError
 * ("cycle detected") for a graph with a cycle.
 */
export function topologicalSort<T>(graph: Graph<T>, key?: (v: T) => unknown): T[] {
  const [V, E0] = graph;
  const kf = key ?? ((v: T) => v);
  const L: T[] = [];
  const E: (readonly [T, T])[] = [...E0];
  const targets = new Set(E.map(([, u]) => valueKey(u)));
  const seen = new Set<string>();
  let S: T[] = [];
  for (const v of V) {
    const k = valueKey(v);
    if (!seen.has(k) && !targets.has(k)) S.push(v);
    seen.add(k);
  }
  // sorted(S, key=key, reverse=True), stable
  S = S.map((v, i) => [v, i] as const)
    .sort((a, b) => compareValues(kf(b[0]), kf(a[0])) || a[1] - b[1])
    .map(([v]) => v);
  while (S.length) {
    const node = S.pop()!;
    L.push(node);
    for (const edge of [...E]) {
      const [u, v] = edge;
      if (!valueEquals(u, node)) continue;
      E.splice(E.findIndex((e) => valueEquals(e[0], u) && valueEquals(e[1], v)), 1);
      if (E.some(([, w]) => valueEquals(w, v))) continue;
      const kv = kf(v);
      const at = S.findIndex((s) => compareValues(kv, kf(s)) > 0);
      if (at >= 0) S.splice(at, 0, v);
      else S.push(v);
    }
  }
  if (E.length) throw new RangeError('cycle detected');
  return L;
}

function stronglyConnected<T>(V: readonly T[], gmap: ValueMap<T, T[]>): T[][] {
  const lowlink = new ValueMap<T, number>();
  const indices = new ValueMap<T, number>();
  const stack: T[] = [];
  const onStack = new Set<string>();
  const callstack: [T, Iterator<T>][] = [];
  const components: T[][] = [];
  const start = (v: T) => {
    const index = stack.length;
    indices.set(v, index);
    lowlink.set(v, index);
    stack.push(v);
    onStack.add(valueKey(v));
    callstack.push([v, (gmap.get(v) ?? [])[Symbol.iterator]()]);
  };
  const finish = (v1: T) => {
    if (lowlink.get(v1) === indices.get(v1)) {
      const pop = () => {
        const x = stack.pop() as T;
        onStack.delete(valueKey(x));
        return x;
      };
      const component = [pop()];
      while (!valueEquals(component[component.length - 1], v1)) component.push(pop());
      components.push(component.reverse());
    }
    const [v2] = callstack.pop()!;
    const top = callstack[callstack.length - 1];
    if (top) {
      const [u] = top;
      lowlink.set(u, Math.min(lowlink.get(u)!, lowlink.get(v2)!));
    }
  };
  for (const v of V) {
    if (indices.has(v)) continue;
    start(v);
    while (callstack.length) {
      const [v1, it1] = callstack[callstack.length - 1]!;
      const r = it1.next();
      if (r.done === true) finish(v1);
      else if (!indices.has(r.value)) start(r.value);
      else if (onStack.has(valueKey(r.value))) lowlink.set(v1, Math.min(lowlink.get(v1)!, indices.get(r.value)!));
    }
  }
  return components;
}

/**
 * SymPy `strongly_connected_components(G)`: the strongly connected
 * components of the directed graph `[V, E]` in reverse topological order
 * (Tarjan's algorithm).
 */
export function stronglyConnectedComponents<T>(G: Graph<T>): T[][] {
  const [V, E] = G;
  const gmap = new ValueMap<T, T[]>();
  for (const v of V) gmap.set(v, []);
  for (const [v1, v2] of E) {
    const g = gmap.get(v1);
    if (!g) throw new RangeError(`edge from a vertex not in the graph: ${String(v1)}`);
    g.push(v2);
  }
  return stronglyConnected(V, gmap);
}

/**
 * SymPy `connected_components(G)`: the connected components of an
 * undirected graph (each edge given in one or both directions), or the
 * weakly connected components of a directed graph.
 */
export function connectedComponents<T>(G: Graph<T>): T[][] {
  const [V, E] = G;
  const undirected: [T, T][] = [];
  for (const [v1, v2] of E) undirected.push([v1, v2], [v2, v1]);
  return stronglyConnectedComponents([V, undirected]);
}

// ---------------------------------------------------------------------------
// rotations

/** SymPy `rotate_left(x, y)`: rotate `x` left by `y` steps. */
export function rotateLeft(x: string, y: number): string;
export function rotateLeft<T>(x: readonly T[], y: number): T[];
export function rotateLeft<T>(x: readonly T[] | string, y: number): T[] | string {
  if (x.length === 0) return typeof x === 'string' ? '' : [];
  const k = ((y % x.length) + x.length) % x.length;
  return typeof x === 'string' ? x.slice(k) + x.slice(0, k) : [...x.slice(k), ...x.slice(0, k)];
}

/** SymPy `rotate_right(x, y)`: rotate `x` right by `y` steps. */
export function rotateRight(x: string, y: number): string;
export function rotateRight<T>(x: readonly T[], y: number): T[];
export function rotateRight<T>(x: readonly T[] | string, y: number): T[] | string {
  if (x.length === 0) return typeof x === 'string' ? '' : [];
  const k = x.length - (((y % x.length) + x.length) % x.length);
  return typeof x === 'string' ? x.slice(k) + x.slice(0, k) : [...x.slice(k), ...x.slice(0, k)];
}

/**
 * SymPy `least_rotation(x, key=None)`: the number of left rotations giving
 * the lexicographically smallest rotation of `x` (Booth's algorithm),
 * elements compared by `key`.
 */
export function leastRotation<T>(x: Sequence<T>, key?: (e: T) => unknown): number {
  const kf = (key ?? ((e: T) => e)) as (e: unknown) => unknown;
  const S: unknown[] = [...(x as Iterable<unknown>), ...(x as Iterable<unknown>)];
  const f: number[] = new Array<number>(S.length).fill(-1);
  let k = 0;
  for (let j = 1; j < S.length; j++) {
    const sj = S[j];
    let i = f[j - k - 1]!;
    while (i !== -1 && !valueEquals(sj, S[k + i + 1])) {
      if (compareValues(kf(sj), kf(S[k + i + 1])) < 0) k = j - i - 1;
      i = f[i]!;
    }
    if (!valueEquals(sj, S[k + i + 1])) {
      if (compareValues(kf(sj), kf(S[k])) < 0) k = j;
      f[j - k] = -1;
    } else {
      f[j - k] = i + 1;
    }
  }
  return k;
}

/**
 * SymPy `minlex(seq, directed=True, key=None)`: the rotation of `seq` that
 * is lexicographically smallest (also considering the reversed sequence when
 * `directed` is false). A string gives a string, other sequences an array.
 */
export function minlex(seq: string, opts?: { directed?: boolean; key?: (e: string) => unknown }): string;
export function minlex<T>(seq: readonly T[], opts?: { directed?: boolean; key?: (e: T) => unknown }): T[];
export function minlex<T>(seq: readonly T[] | string, opts: { directed?: boolean; key?: (e: T) => unknown } = {}): T[] | string {
  const key = opts.key;
  const rot = (s: readonly T[] | string): readonly T[] | string => {
    const k = leastRotation(s as Sequence<T>, key);
    return typeof s === 'string' ? rotateLeft(s, k) : rotateLeft(s, k);
  };
  let best = rot(seq);
  if (opts.directed === false) {
    const rseq = typeof seq === 'string' ? seq.split('').reverse().join('') : [...seq].reverse();
    const rbest = rot(rseq);
    // min(best, rbest, key=key): the key applies to the whole sequences
    const kf = (key ?? ((e: unknown) => e)) as (e: unknown) => unknown;
    if (compareValues(kf(rbest), kf(best)) < 0) best = rbest;
  }
  return typeof best === 'string' ? best : [...best];
}

/**
 * SymPy `runs(seq, op=gt)`: split `seq` into runs in which each element
 * relates to the previous one by `op(next, previous)` (by default `>`).
 */
export function runs<T>(seq: Iterable<T>, op: (a: T, b: T) => boolean = (a, b) => compareValues(a, b) > 0): T[][] {
  const cycles: T[][] = [];
  let run: T[] | undefined;
  for (const ei of seq) {
    if (run === undefined) run = [ei];
    else if (op(ei, run[run.length - 1]!)) run.push(ei);
    else {
      cycles.push(run);
      run = [ei];
    }
  }
  if (run) cycles.push(run);
  return cycles;
}

/**
 * SymPy `rotations(s, dir=1)`: the rotations of `s`, each rotated left
 * (or right with `dir = -1`) relative to the previous one.
 */
export function* rotations<T>(s: Iterable<T>, dir = 1): Generator<T[], void, undefined> {
  let seq = [...s];
  const n = seq.length;
  for (let i = 0; i < n; i++) {
    yield seq;
    seq = rotateLeft(seq, dir);
  }
}

/** SymPy `roundrobin(*iterables)`: items taken from each iterable in turn. */
export function* roundrobin<T>(...iterables: Iterable<T>[]): Generator<T, void, undefined> {
  let its = iterables.map((it) => it[Symbol.iterator]());
  while (its.length) {
    const next: Iterator<T>[] = [];
    for (const it of its) {
      const r = it.next();
      if (r.done === true) continue;
      yield r.value;
      next.push(it);
    }
    its = next;
  }
}

// ---------------------------------------------------------------------------
// combinatorial generators

/** One [element, count] entry of a multiset in list form. */
type MultisetEntry<T> = [T, number];

const multisetCombinationsG = function* <T>(n: number, g: readonly MultisetEntry<T>[]): Generator<T[], void, undefined> {
  const N = g.reduce((a, [, v]) => a + v, 0);
  if (n > N || !n) {
    yield [];
    return;
  }
  for (let i = 0; i < g.length; i++) {
    const [k, v0] = g[i]!;
    let v = v0;
    if (v >= n) {
      yield new Array<T>(n).fill(k);
      v = n - 1;
    }
    for (let w = Math.min(n, v); w > 0; w--) {
      for (const j of multisetCombinationsG(n - w, g.slice(i + 1))) {
        const rv = [...new Array<T>(w).fill(k), ...j];
        if (rv.length === n) yield rv;
      }
    }
  }
};

function checkCounts(m: ReadonlyMap<unknown, number>): void {
  for (const v of m.values()) {
    checkInt(v, 'count');
    if (v < 0) throw new RangeError('counts cannot be negative');
  }
}

/**
 * SymPy `multiset_combinations(m, n)`: the unique combinations of size `n`
 * of the multiset `m` (a sequence, a string or a map from element to
 * multiplicity).
 */
export function* multisetCombinations<T>(m: Iterable<T> | ReadonlyMap<T, number>, n: number): Generator<T[], void, undefined> {
  let g: MultisetEntry<T>[];
  if (m instanceof Map) {
    const mm = m as ReadonlyMap<T, number>;
    checkCounts(mm);
    const N = [...mm.values()].reduce((a, b) => a + b, 0);
    if (n > N) return;
    g = orderedValues(mm.keys()).map((k) => [k, mm.get(k)!]);
  } else {
    const items = [...(m as Iterable<T>)];
    if (n > items.length) return;
    const ms = multiset(items);
    g = orderedValues(ms.keys()).map((k) => [k, ms.get(k)!]);
  }
  yield* multisetCombinationsG(n, g);
}

const multisetPermutationsG = function* <T>(size: number | null, g: MultisetEntry<T>[]): Generator<T[], void, undefined> {
  const doo = g.filter((gi) => gi[1] > 0);
  const SUM = doo.reduce((a, [, v]) => a + v, 0);
  if (!doo.length || (size !== null && (size > SUM || size < 1))) {
    if ((!doo.length && size === null) || size === 0) yield [];
    return;
  }
  if (size === 1) {
    for (const [k] of doo) yield [k];
  } else if (doo.length === 1) {
    const [k, v] = doo[0]!;
    const c = size === null ? v : size <= v ? size : 0;
    yield new Array<T>(c).fill(k);
  } else if (doo.every(([, v]) => v === 1)) {
    yield* permutations(
      doo.map(([k]) => k),
      size,
    );
  } else {
    const sz = size ?? SUM;
    for (const entry of doo) {
      const [k] = entry;
      entry[1] -= 1;
      for (const j of multisetPermutationsG(sz - 1, doo)) if (j.length) yield [k, ...j];
      entry[1] += 1;
    }
  }
};

/**
 * SymPy `multiset_permutations(m, size=None)`: the unique permutations of
 * the multiset `m` (a sequence, a string or a map from element to
 * multiplicity), optionally of the given size.
 */
export function* multisetPermutations<T>(m: Iterable<T> | ReadonlyMap<T, number>, size?: number | null): Generator<T[], void, undefined> {
  let g: MultisetEntry<T>[];
  if (m instanceof Map) {
    const mm = m as ReadonlyMap<T, number>;
    checkCounts(mm);
    g = orderedValues(mm.keys()).map((k) => [k, mm.get(k)!]);
  } else {
    g = group(orderedValues(m as Iterable<T>), { multiple: false });
  }
  yield* multisetPermutationsG(size ?? null, g);
}

const setPartitions = function* (n: number): Generator<[number, number[]], void, undefined> {
  const p: number[] = new Array<number>(n).fill(0);
  const q: number[] = new Array<number>(n).fill(0);
  let nc = 1;
  yield [nc, q];
  while (nc !== n) {
    let m = n;
    let i: number;
    for (;;) {
      m -= 1;
      i = q[m]!;
      if (p[i] !== 1) break;
      q[m] = 0;
    }
    i += 1;
    q[m] = i;
    m += 1;
    nc += m - n;
    p[0]! += n - m;
    if (i === nc) {
      p[nc] = 0;
      nc += 1;
    }
    p[i - 1]! -= 1;
    p[i]! += 1;
    yield [nc, q];
  }
};

/**
 * SymPy `multiset_partitions(multiset, m=None)`: the unique partitions of
 * the multiset (a sequence or string; an integer `n` stands for
 * `[0, 1, ..., n - 1]`), only those with `m` parts when `m` is given.
 * A string is the multiset of its characters (SymPy partitions a string of
 * one repeated character into strings, e.g. `['a', 'aa']`; symjs gives
 * `[['a'], ['a', 'a']]`).
 */
export function multisetPartitions(multiset: number, m?: number | null): Generator<number[][], void, undefined>;
export function multisetPartitions(multiset: string, m?: number | null): Generator<string[][], void, undefined>;
export function multisetPartitions<T>(multiset: Iterable<T>, m?: number | null): Generator<T[][], void, undefined>;
export function* multisetPartitions<T>(multiset: Iterable<T> | number, m?: number | null): Generator<unknown[][], void, undefined> {
  const mm = m ?? null;
  if (typeof multiset === 'number') {
    const n = checkInt(multiset, 'multiset');
    if (mm && mm > n) return;
    if (n === 0) {
      // the empty set has one partition, without parts (SymPy raises IndexError)
      if (!mm) yield [];
      return;
    }
    const ms = Array.from({ length: n }, (_, i) => i);
    if (mm === 1) {
      yield [[...ms]];
      return;
    }
    for (const [nc, q] of setPartitions(n)) {
      if (mm === null || nc === mm) {
        const rv: number[][] = Array.from({ length: nc }, () => []);
        for (let i = 0; i < n; i++) rv[q[i]!]!.push(ms[i]!);
        yield rv;
      }
    }
    return;
  }
  const items = [...multiset];
  if (!hasVariety(items)) {
    const n = items.length;
    if (mm && mm > n) return;
    if (mm === 1) {
      yield [[...items]];
      return;
    }
    const x = items.slice(0, 1);
    for (const [size, p] of partitions(n, { m: mm, size: true })) {
      if (mm === null || size === mm) {
        const rv: T[][] = [];
        for (const k of [...p.keys()].sort((a, b) => a - b)) {
          for (let r = 0; r < p.get(k)!; r++) rv.push(Array.from({ length: k }, () => x[0]!));
        }
        yield rv;
      }
    }
    return;
  }
  const ms = orderedValues(items);
  const n = ms.length;
  if (mm && mm > n) return;
  if (mm === 1) {
    yield [[...ms]];
    return;
  }
  const grouped = group(ms, { multiple: false });
  const elements = grouped.map(([e]) => e);
  const multiplicities = grouped.map(([, c]) => c);
  if (elements.length < ms.length) {
    if (mm) {
      const mpt = new MultisetPartitionTraverser();
      for (const state of mpt.enumRange(multiplicities, mm - 1, mm)) yield listVisitor(state, elements);
    } else {
      for (const state of multisetPartitionsTaocp(multiplicities)) yield listVisitor(state, elements);
    }
  } else {
    for (const [nc, q] of setPartitions(n)) {
      if (mm === null || nc === mm) {
        const rv: number[][] = Array.from({ length: nc }, () => []);
        for (let i = 0; i < n; i++) rv[q[i]!]!.push(i);
        yield rv.map((part) => part.map((j) => ms[j]!));
      }
    }
  }
}

/**
 * SymPy `partitions(n, m=None, k=None, size=False)`: the partitions of the
 * positive integer `n` as maps from part to multiplicity, with at most `m`
 * parts and parts at most `k`; with `size: true`, `[number of parts, map]`
 * pairs. Invalid input gives the single empty partition, as in SymPy.
 */
export function partitions(n: number, opts?: { m?: number | null; k?: number | null; size?: false }): Generator<Map<number, number>, void, undefined>;
export function partitions(n: number, opts: { m?: number | null; k?: number | null; size: true }): Generator<[number, Map<number, number>], void, undefined>;
export function* partitions(
  n: number,
  opts: { m?: number | null; k?: number | null; size?: boolean } = {},
): Generator<Map<number, number> | [number, Map<number, number>], void, undefined> {
  const size = opts.size === true;
  const m0 = opts.m ?? null;
  const k0 = opts.k ?? null;
  const out = (ms: Map<number, number>): Map<number, number> | [number, Map<number, number>] => {
    const copy = new Map(ms);
    if (!size) return copy;
    let s = 0;
    for (const v of copy.values()) s += v;
    return [s, copy];
  };
  if (n <= 0 || (m0 !== null && m0 < 1) || (k0 !== null && k0 < 1) || (m0 !== null && k0 !== null && m0 * k0 < n)) {
    yield out(new Map());
    return;
  }
  checkInt(n, 'n');
  const m = m0 === null ? n : checkInt(Math.min(m0, n), 'm');
  const k = checkInt(Math.min(k0 ?? n, n), 'k');
  let q = Math.floor(n / k);
  let r = n % k;
  const ms = new Map<number, number>([[k, q]]);
  const keys = [k];
  if (r) {
    ms.set(r, 1);
    keys.push(r);
  }
  let room = m - q - (r ? 1 : 0);
  yield out(ms);
  while (!(keys.length === 1 && keys[0] === 1)) {
    let reuse: number;
    if (keys[keys.length - 1] === 1) {
      keys.pop();
      reuse = ms.get(1)!;
      ms.delete(1);
      room += reuse;
    } else {
      reuse = 0;
    }
    let need: number;
    for (;;) {
      let i = keys[keys.length - 1]!;
      const newcount = ms.get(i)! - 1;
      ms.set(i, newcount);
      reuse += i;
      if (newcount === 0) {
        keys.pop();
        ms.delete(i);
      }
      room += 1;
      i -= 1;
      q = Math.floor(reuse / i);
      r = reuse % i;
      need = q + (r ? 1 : 0);
      if (need > room) {
        if (!keys.length) return;
        continue;
      }
      ms.set(i, q);
      keys.push(i);
      if (r) {
        ms.set(r, 1);
        keys.push(r);
      }
      break;
    }
    room -= need;
    yield out(ms);
  }
}

/**
 * SymPy `ordered_partitions(n, m=None, sort=True)`: the partitions of `n`
 * as ascending lists in lexicographic order, only those with `m` parts when
 * `m` is given (unordered among themselves when `sort` is false and m
 * divides n). SymPy reuses one list for the partitions when `m` is given;
 * symjs yields a fresh array each time.
 */
export function* orderedPartitions(n: number, m?: number | null, opts: { sort?: boolean } = {}): Generator<number[], void, undefined> {
  for (const p of orderedPartitionsInPlace(n, m ?? null, opts.sort ?? true)) yield [...p];
}

const orderedPartitionsInPlace = function* (n: number, m: number | null, sort: boolean): Generator<number[], void, undefined> {
  if (n < 1 || (m !== null && m < 1)) {
    yield [];
    return;
  }
  if (m === null) {
    const a: number[] = new Array<number>(n).fill(1);
    let y = -1;
    let v = n;
    while (v > 0) {
      v -= 1;
      let x = a[v]! + 1;
      while (y >= 2 * x) {
        a[v] = x;
        y -= x;
        v += 1;
      }
      const w = v + 1;
      while (x <= y) {
        a[v] = x;
        a[w] = y;
        yield a.slice(0, w + 1);
        x += 1;
        y -= 1;
      }
      a[v] = x + y;
      y = a[v]! - 1;
      yield a.slice(0, w);
    }
  } else if (m === 1) {
    yield [n];
  } else if (n === m) {
    yield new Array<number>(n).fill(1);
  } else {
    for (let b = 1; b <= Math.floor(n / m); b++) {
      const a: number[] = new Array<number>(m).fill(b);
      const x = n - b * m;
      if (!x) {
        if (sort) yield a;
      } else if (!sort && x <= m) {
        for (const ax of orderedPartitionsInPlace(x, null, false)) {
          const mi = ax.length;
          a.splice(m - mi, mi, ...ax.map((i) => i + b));
          yield a;
          a.splice(m - mi, mi, ...new Array<number>(mi).fill(b));
        }
      } else {
        for (let mi = 1; mi < m; mi++) {
          for (const ax of orderedPartitionsInPlace(x, mi, true)) {
            a.splice(m - mi, mi, ...ax.map((i) => i + b));
            yield a;
            a.splice(m - mi, mi, ...new Array<number>(mi).fill(b));
          }
        }
      }
    }
  }
};

/**
 * SymPy `binary_partitions(n)`: the partitions of `n` into powers of two,
 * in decreasing order (TAOCP 7.2.1.5, problem 64). SymPy reuses one list;
 * symjs yields a fresh array each time.
 */
export function* binaryPartitions(n: number): Generator<number[], void, undefined> {
  checkInt(n, 'n');
  let power = 2 ** Math.ceil(Math.log2(n));
  let acc = 0;
  const partition: number[] = [];
  while (power >= 1) {
    if (acc + power <= n) {
      partition.push(power);
      acc += power;
    }
    power = Math.floor(power / 2);
  }
  let lastNum = partition.length - 1 - (n & 1);
  while (lastNum >= 0) {
    yield [...partition];
    if (partition[lastNum] === 2) {
      partition[lastNum] = 1;
      partition.push(1);
      lastNum -= 1;
      continue;
    }
    partition.push(1);
    partition[lastNum] = partition[lastNum]! >> 1;
    let x = partition[lastNum]!;
    partition[lastNum + 1] = x;
    lastNum += 1;
    while (x > 1) {
      if (x <= partition.length - lastNum - 1) {
        partition.splice(partition.length - x + 1);
        lastNum += 1;
        partition[lastNum] = x;
      } else {
        x >>= 1;
      }
    }
  }
  yield new Array<number>(n).fill(1);
}

/**
 * SymPy `has_dups(seq)`: whether `seq` has duplicate elements (always
 * false for a `Set` or `Map`).
 */
export function hasDups(seq: Iterable<unknown>): boolean {
  if (seq instanceof Set || seq instanceof Map) return false;
  const seen = new Set<string>();
  for (const s of seq) {
    const k = valueKey(s);
    if (seen.has(k)) return true;
    seen.add(k);
  }
  return false;
}

/** SymPy `has_variety(seq)`: whether `seq` has two different elements. */
export function hasVariety(seq: Iterable<unknown>): boolean {
  let first = true;
  let sentinel: unknown;
  for (const s of seq) {
    if (first) {
      sentinel = s;
      first = false;
    } else if (!valueEquals(s, sentinel)) {
      return true;
    }
  }
  return false;
}

/**
 * SymPy `uniq(seq)`: the unique elements of `seq` in order of first
 * appearance (arrays and other unhashable values included). Throws a
 * RangeError when an array changes size during the iteration.
 */
export function* uniq<T>(seq: Iterable<T>): Generator<T, void, undefined> {
  const n = Array.isArray(seq) ? seq.length : null;
  const seen = new Set<string>();
  for (const s of seq) {
    const k = valueKey(s);
    if (seen.has(k)) continue;
    seen.add(k);
    yield s;
    if (n !== null && (seq as readonly T[]).length !== n) throw new RangeError('sequence changed size during iteration');
  }
}

/**
 * SymPy `generate_bell(n)`: the permutations of `[0, ..., n - 1]` in which
 * each differs from the previous one by swapping two neighbours
 * (Steinhaus-Johnson-Trotter order).
 */
export function* generateBell(n: number): Generator<number[], void, undefined> {
  checkInt(n, 'n');
  if (n < 1) throw new RangeError('n must be a positive integer');
  if (n === 1) {
    yield [0];
  } else if (n === 2) {
    yield [0, 1];
    yield [1, 0];
  } else if (n === 3) {
    for (const p of [
      [0, 1, 2],
      [0, 2, 1],
      [2, 0, 1],
      [2, 1, 0],
      [1, 2, 0],
      [1, 0, 2],
    ]) {
      yield p;
    }
  } else {
    const m = n - 1;
    const op = [0, ...new Array<number>(m).fill(-1)];
    const l = Array.from({ length: n }, (_, i) => i);
    for (;;) {
      yield [...l];
      let big = -1;
      let bigValue = -1;
      for (let i = 0; i < n; i++) {
        if (op[i] && l[i]! > bigValue) {
          big = i;
          bigValue = l[i]!;
        }
      }
      if (big < 0) break;
      const i = big;
      const j = i + op[i]!;
      [l[i], l[j]] = [l[j]!, l[i]!];
      [op[i], op[j]] = [op[j]!, op[i]!];
      const lj = at(l, j);
      if (j === 0 || j === m || at(l, j + at(op, j)) > lj) op[j] = 0;
      for (let t = 0; t < j; t++) if (at(l, t) > lj) op[t] = 1;
      for (let t = j + 1; t < n; t++) if (at(l, t) > lj) op[t] = -1;
    }
  }
}

/** SymPy `generate_involutions(n)`: the permutations of `[0, ..., n - 1]` that are their own inverse. */
export function* generateInvolutions(n: number): Generator<number[], void, undefined> {
  const idx = Array.from({ length: n }, (_, i) => i);
  for (const p of permutations(idx)) {
    if (idx.every((i) => p[p[i]!] === i)) yield p;
  }
}

const setDerangements = function* <T>(s: readonly T[]): Generator<T[], void, undefined> {
  if (s.length < 2) return;
  if (s.length === 2) {
    yield [s[1]!, s[0]!];
    return;
  }
  if (s.length === 3) {
    yield [s[1]!, s[2]!, s[0]!];
    yield [s[2]!, s[0]!, s[1]!];
    return;
  }
  for (const p of permutations(s)) {
    if (!p.some((x, i) => valueEquals(x, s[i]))) yield p;
  }
};

/**
 * SymPy `multiset_derangements(s)`: the derangements of the multiset `s`
 * (arrangements with no element in its original position). SymPy fills
 * one list in place; symjs yields a fresh array each time.
 */
export function* multisetDerangements<T>(s: Iterable<T>): Generator<T[], void, undefined> {
  const seq = [...s];
  const ms = multiset(seq);
  const n = seq.length;
  if (n === 0) return;
  const mx = Math.max(...ms.values());
  // one element fills more than half of the positions: no derangement
  if (mx * 2 > n) return;
  // all elements appear once
  if (ms.size === n) {
    yield* setDerangements(seq);
    return;
  }
  let M = seq[0] as T;
  for (const [k, v] of ms) {
    if (v === mx) {
      M = k;
      break;
    }
  }
  const inonM: number[] = [];
  const iM: number[] = [];
  for (let i = 0; i < n; i++) (valueEquals(seq[i], M) ? iM : inonM).push(i);
  const rv: (T | undefined)[] = new Array<T | undefined>(n).fill(undefined);
  const emit = (): T[] => [...rv] as T[];

  // half are the same
  if (2 * mx === n) {
    for (const i of inonM) rv[i] = M;
    for (const p of multisetPermutations(inonM.map((i) => seq[i]!))) {
      iM.forEach((i, t) => (rv[i] = p[t]));
      yield emit();
    }
    return;
  }
  // a single repeat covers all but one of the non-repeats
  if (n - 2 * mx === 1 && ms.size === n - mx + 1) {
    for (let i = 0; i < inonM.length; i++) {
      const i1 = inonM[i]!;
      const ifill = [...inonM.slice(0, i), ...inonM.slice(i + 1)];
      for (const j of ifill) rv[j] = M;
      for (const p of permutations(ifill.map((j) => seq[j]!))) {
        rv[i1] = seq[i1];
        iM.forEach((j, t) => (rv[j] = p[t]));
        let k = i1;
        for (const j of iM) {
          [rv[j], rv[k]] = [rv[k], rv[j]];
          yield emit();
          k = j;
        }
      }
    }
    return;
  }
  // general case: place the elements in order of decreasing multiplicity
  const takeList = [...ms].sort((a, b) => a[1] - b[1] || compareValues(a[0], b[0]));
  const iopen = (v: T): number[] => {
    const out: number[] = [];
    for (let i = 0; i < n; i++) if (rv[i] === undefined && !valueEquals(seq[i], v)) out.push(i);
    return out;
  };
  function* finishDerangements(): Generator<T[], void, undefined> {
    const [a, aCt] = takeList[1]!;
    const [b, bCt] = takeList[0]!;
    const forcedA: number[] = [];
    const forcedB: number[] = [];
    const openFree: number[] = [];
    for (let i = 0; i < n; i++) {
      if (rv[i] !== undefined) continue;
      if (valueEquals(seq[i], a)) forcedB.push(i);
      else if (valueEquals(seq[i], b)) forcedA.push(i);
      else openFree.push(i);
    }
    if (forcedA.length > aCt || forcedB.length > bCt) return;
    for (const i of forcedA) rv[i] = a;
    for (const i of forcedB) rv[i] = b;
    for (const aPlace of combinations(openFree, aCt - forcedA.length)) {
      for (const p of aPlace) rv[p] = a;
      for (const i of openFree) rv[i] ??= b;
      yield emit();
      for (const i of openFree) rv[i] = undefined;
    }
    for (const i of forcedA) rv[i] = undefined;
    for (const i of forcedB) rv[i] = undefined;
  }
  function* doPlace(j: number): Generator<T[], void, undefined> {
    if (j === 1) {
      yield* finishDerangements();
      return;
    }
    const [E, c] = takeList[j]!;
    for (const places of combinations(iopen(E), c)) {
      for (const p of places) rv[p] = E;
      yield* doPlace(j - 1);
      for (const p of places) rv[p] = undefined;
    }
  }
  yield* doPlace(takeList.length - 1);
}

/** A seeded pseudorandom choice (mulberry32). */
function seededChoice(seed: number): <T>(xs: readonly T[]) => T {
  let a = seed >>> 0;
  const next = (): number => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  return <T>(xs: readonly T[]): T => xs[Math.floor(next() * xs.length)]!;
}

const defaultChoice = <T>(xs: readonly T[]): T => xs[Math.floor(Math.random() * xs.length)]!;

/** A function picking one element of a nonempty array. */
export type Choice = <T>(xs: readonly T[]) => T;

/**
 * SymPy `random_derangement(t, choice=None, strict=True)`: a random
 * arrangement of `t` with no element in its original position. `choice`
 * picks an element of an array; pass a number instead to seed a
 * reproducible generator. When an element fills more than half of the
 * positions no derangement exists: a RangeError is thrown, or with
 * `strict: false` some of those elements stay in place. The result is an
 * array (of characters for a string; SymPy returns a string in the
 * non-strict case only).
 */
export function randomDerangement<T>(t: Iterable<T>, choice?: Choice | number | null, opts: { strict?: boolean } = {}): T[] {
  const pick1: Choice = typeof choice === 'number' ? seededChoice(choice) : (choice ?? defaultChoice);
  return derange([...t], pick1, opts.strict ?? true);
}

function derange<T>(t: readonly T[], choice: Choice, strict: boolean): T[] {
  const shuffle = <E>(rv: E[]) => {
    for (let i = rv.length - 1; i > 0; i--) {
      const x = choice(rv.slice(0, i + 1));
      const j = rv.findIndex((e) => valueEquals(e, x));
      [rv[i], rv[j]] = [rv[j]!, rv[i]!];
    }
  };
  const pick = <E>(rv: E[], k: number): E[] => {
    shuffle(rv);
    return rv.slice(0, k);
  };
  const ms = [...multiset(t)].map((e, i) => [e, i] as const).sort((a, b) => a[0][1] - b[0][1] || a[1] - b[1]).map(([e]) => e);
  const tot = t.length;
  if (tot === 0) return [];
  const [M, mx] = ms[ms.length - 1]!;
  const n = t.length;
  const xs = 2 * mx - tot;
  if (xs > 0) {
    if (strict) throw new RangeError('no derangement possible');
    const opts = t.flatMap((c, i) => (valueEquals(c, M) ? [i] : []));
    pick(opts, xs);
    const stay = opts.slice(0, xs).sort((a, b) => a - b);
    let rv = [...t];
    for (const i of [...stay].reverse()) rv.splice(i, 1);
    rv = derange(rv, choice, strict);
    for (const i of stay) rv.splice(i, 0, M);
    return rv;
  }
  if (n === ms.length) {
    const rv = [...t];
    for (;;) {
      shuffle(rv);
      if (rv.every((x, i) => !valueEquals(x, t[i]))) return rv;
    }
  }
  const rv: (T | undefined)[] = new Array<T | undefined>(n).fill(undefined);
  for (;;) {
    let ok = true;
    for (let j = ms.length - 1; j >= 0; j--) {
      const [e, c] = ms[j]!;
      const opts: number[] = [];
      for (let i = 0; i < n; i++) if (rv[i] === undefined && !valueEquals(t[i], e)) opts.push(i);
      if (opts.length < c) {
        rv.fill(undefined);
        ok = false;
        break;
      }
      pick(opts, c);
      for (let i = 0; i < c; i++) rv[opts[i]!] = e;
    }
    if (ok) return rv as T[];
  }
}

/**
 * SymPy `generate_derangements(s)`: the unique derangements of the
 * elements of `s`.
 */
export function* generateDerangements<T>(s: Iterable<T>): Generator<T[], void, undefined> {
  const seq = [...s];
  if (!hasDups(seq)) yield* setDerangements(seq);
  else yield* multisetDerangements(seq);
}

/**
 * SymPy `necklaces(n, k, free=False)`: the necklaces of `n` beads with `k`
 * colours (sequences equal up to rotation), or bracelets (also up to
 * reflection) with `free: true` (FKM algorithm).
 */
export function* necklaces(n: number, k: number, opts: { free?: boolean } = {}): Generator<number[], void, undefined> {
  const free = opts.free === true;
  if (k === 0 && n > 0) return;
  const a: number[] = new Array<number>(n).fill(0);
  yield [...a];
  if (n === 0) return;
  for (;;) {
    let i = n - 1;
    while (a[i] === k - 1) {
      i -= 1;
      if (i === -1) return;
    }
    a[i]! += 1;
    for (let j = 0; j < n - i - 1; j++) a[j + i + 1] = a[j]!;
    if (n % (i + 1) === 0) {
      let ok = true;
      if (free) {
        for (let j = 0; j < n - 1 && ok; j++) {
          // a <= a[j::-1] + a[-1:j:-1]
          const rev = [...a.slice(0, j + 1).reverse(), ...a.slice(j + 1).reverse()];
          ok = compareValues(a, rev) <= 0;
        }
      }
      if (ok) yield [...a];
    }
  }
}

/** SymPy `bracelets(n, k)`: the free necklaces (`necklaces(n, k, { free: true })`). */
export function bracelets(n: number, k: number): Generator<number[], void, undefined> {
  return necklaces(n, k, { free: true });
}

/**
 * SymPy `generate_oriented_forest(n)`: the oriented forests on `n` nodes as
 * parent-pointer lists (Beyer and Hedetniemi).
 */
export function* generateOrientedForest(n: number): Generator<number[], void, undefined> {
  const P = Array.from({ length: n + 1 }, (_, i) => i - 1);
  for (;;) {
    yield P.slice(1);
    if (P[n]! > 0) {
      P[n] = P[P[n]!]!;
    } else {
      let found = false;
      for (let p = n - 1; p > 0; p--) {
        if (P[p] !== 0) {
          const target = P[p]! - 1;
          let q = p - 1;
          for (; q > 0; q--) if (P[q] === target) break;
          const offset = p - q;
          for (let i = p; i <= n; i++) P[i] = P[i - offset]!;
          found = true;
          break;
        }
      }
      if (!found) break;
    }
  }
}

/**
 * SymPy `sequence_partitions(l, n)`: the ways to split the nonempty
 * sequence `l` into `n` nonempty consecutive pieces.
 */
export function sequencePartitions(l: string, n: number): Generator<string[], void, undefined>;
export function sequencePartitions<T>(l: readonly T[], n: number): Generator<T[][], void, undefined>;
export function* sequencePartitions<T>(l: readonly T[] | string, n: number): Generator<(T[] | string)[], void, undefined> {
  if (n === 1 && l.length) {
    yield [typeof l === 'string' ? l : [...l]];
    return;
  }
  for (let i = 1; i < l.length; i++) {
    for (const part of sequencePartitions(l.slice(i) as readonly T[], n - 1)) yield [l.slice(0, i), ...part];
  }
}

/**
 * SymPy `sequence_partitions_empty(l, n)`: the ways to split the sequence
 * `l` into `n` consecutive (possibly empty) pieces.
 */
export function sequencePartitionsEmpty(l: string, n: number): Generator<string[], void, undefined>;
export function sequencePartitionsEmpty<T>(l: readonly T[], n: number): Generator<T[][], void, undefined>;
export function* sequencePartitionsEmpty<T>(l: readonly T[] | string, n: number): Generator<(T[] | string)[], void, undefined> {
  if (n < 1) return;
  if (n === 1) {
    yield [typeof l === 'string' ? l : [...l]];
    return;
  }
  for (let i = 0; i <= l.length; i++) {
    for (const part of sequencePartitionsEmpty(l.slice(i) as readonly T[], n - 1)) yield [l.slice(0, i), ...part];
  }
}

/**
 * SymPy `kbins(l, k, ordered=None)`: `l` partitioned into `k` bins.
 * `ordered` is `null` (consecutive pieces, no reordering) or one of
 * `0` (`00`), `1` (`01`), `10` and `11`: whether the order of the bins
 * (first digit) and of the items in the bins (second digit) matters.
 */
export function* kbins<T>(l: readonly T[], k: number, ordered: number | null = null): Generator<T[][], void, undefined> {
  if (ordered === null) {
    yield* sequencePartitions(l, k);
  } else if (ordered === 11) {
    for (const pl of multisetPermutations(l)) yield* sequencePartitions(pl, k);
  } else if (ordered === 0) {
    yield* multisetPartitions(l, k);
  } else if (ordered === 10) {
    for (const p of multisetPartitions(l, k)) yield* permutations(p);
  } else if (ordered === 1) {
    for (const [kgot, p] of partitions(l.length, { m: k, size: true })) {
      if (kgot !== k) continue;
      const sizes = [...p].sort((a, b) => a[0] - b[0]);
      for (const li of multisetPermutations(l)) {
        const rv: T[][] = [];
        let i = 0;
        for (const [size, multiplicity] of sizes) {
          for (let r = 0; r < multiplicity; r++) {
            rv.push(li.slice(i, i + size));
            i += size;
          }
        }
        yield rv;
      }
    }
  } else {
    throw new RangeError(`ordered must be one of 00, 01, 10 or 11, not ${ordered}`);
  }
}

/** A value whose sign can be changed: a number, a bigint or an expression. */
export type Signed = number | bigint | Expr;

const isZeroValue = (x: Signed): boolean => (x instanceof Expr ? isNum(x) && x.isZero : x === 0 || x === 0n);
const negate = (x: Signed): Signed => (typeof x === 'number' ? -x : typeof x === 'bigint' ? -x : neg(x));

/**
 * SymPy `permute_signs(t)`: `t` with every combination of signs of its
 * nonzero elements.
 */
export function* permuteSigns<S extends Signed>(t: readonly S[]): Generator<S[], void, undefined> {
  const nz = t.filter((x) => !isZeroValue(x)).length;
  for (const signs of product(Array.from({ length: nz }, () => [1, -1]))) {
    const ss = [...signs];
    yield t.map((x) => (isZeroValue(x) ? x : ss.pop() === -1 ? (negate(x) as S) : x));
  }
}

/**
 * SymPy `signed_permutations(t)`: the unique permutations of `t` with every
 * combination of signs of the nonzero elements.
 */
export function* signedPermutations<S extends Signed>(t: readonly S[]): Generator<S[], void, undefined> {
  for (const j of multisetPermutations(t)) yield* permuteSigns(j);
}

/**
 * SymPy `postorder_traversal(node, keys=None)`: the subtrees of `node`
 * (an expression, or an iterable of expressions and iterables) in
 * post-order. With `keys`, the arguments of each node are visited in the
 * order given by `ordered` (`true` for the default keys).
 */
export function* postorderTraversal(node: unknown, keys?: boolean | KeyFunction<Expr> | readonly KeyFunction<Expr>[] | null): Generator<unknown, void, undefined> {
  if (node instanceof Expr) {
    let args: readonly Expr[] = node.args;
    if (keys !== undefined && keys !== null && keys !== false) {
      args = keys === true ? orderedValues(args) : orderedValues(args, keys, false);
    }
    for (const arg of args) yield* postorderTraversal(arg, keys);
  } else if (iterable(node)) {
    for (const item of node as Iterable<unknown>) yield* postorderTraversal(item, keys);
  }
  yield node;
}
