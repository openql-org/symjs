// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/simplify/epathtools.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file Manipulation of expressions using paths (a port of SymPy's
 * epathtools: EPath and epath).
 */

import { Add, Expr, Mul } from '../core/nodes';
import { sympify } from '../core/ops';
import { NotImplementedError } from '../core/errors';
import { asOrderedFactors, asOrderedTerms } from '../printing/sortkey';
import { isSympyAtom, sympyArgs, sympyClassBases, sympyClassName, sympyRebuild } from './csemain';

/** A function applied by {@link EPath.apply} to a selected part (with the extra arguments). */
export type EPathFunction<P = Expr> = (part: P, ...args: never[]) => unknown;

/** An argument of a rebuilt expression (SymPy sympifies the results of func). */
function toExpr(x: unknown): Expr {
  if (x instanceof Expr || typeof x === 'number' || typeof x === 'bigint') return sympify(x);
  throw new TypeError('epath: a part of an expression must become an expression');
}

/** A slice `[start:stop:step]` of a selector (null for an omitted bound). */
type Slice = { start: number | null; stop: number | null; step: number | null };
/** A compiled selector: attributes, types and an index or slice (null: all). */
type Selector = { attrs: string[]; types: string[]; span: number | Slice | null };

/** Python int(): an optional sign and digits (surrounding whitespace allowed). */
function parseInt10(s: string): number {
  const t = s.trim();
  if (!/^[-+]?\d+$/.test(t)) throw new RangeError(`invalid literal for int() with base 10: '${s}'`);
  return Number(t);
}

function compileSelector(selectorIn: string): Selector {
  let selector = selectorIn.trim();
  if (!selector) throw new RangeError('empty selector');
  const stop = selector.search(/[^\p{L}\p{N}_|?]/u);
  const index = stop < 0 ? selector.length : stop;
  const attrs: string[] = [];
  const types: string[] = [];
  if (index) {
    const elements = selector.slice(0, index);
    selector = selector.slice(index);
    for (const element0 of elements.split('|')) {
      const element = element0.trim();
      if (!element) throw new RangeError('empty element');
      if (element.endsWith('?')) attrs.push(element.slice(0, -1));
      else types.push(element);
    }
  }
  let span: number | Slice | null = null;
  if (selector !== '*') {
    if (selector.startsWith('[')) {
      const i = selector.indexOf(']');
      if (i < 0) throw new RangeError("expected ']', got EOL");
      const spanText = selector.slice(1, i);
      if (!spanText.includes(':')) span = parseInt10(spanText);
      else {
        const parts = spanText.split(':');
        if (parts.length > 3) throw new TypeError(`slice expected at most 3 arguments, got ${parts.length}`);
        const [start, stop, step] = [0, 1, 2].map((k) => {
          const elt = parts[k];
          return elt === undefined || !elt ? null : parseInt10(elt);
        });
        span = { start: start ?? null, stop: stop ?? null, step: step ?? null };
      }
      selector = selector.slice(i + 1);
    }
    if (selector) throw new RangeError('trailing characters in selector');
  }
  return { attrs, types, span };
}

/** Python slice.indices(n) as the list of selected indices. */
function sliceIndices(s: Slice, n: number): number[] {
  const step = s.step ?? 1;
  if (step === 0) throw new RangeError('slice step cannot be zero');
  const clamp = (v: number | null, dflt: number, lo: number, hi: number): number => {
    if (v === null) return dflt;
    const w = v < 0 ? v + n : v;
    return Math.min(Math.max(w, lo), hi);
  };
  const out: number[] = [];
  if (step > 0) {
    const start = clamp(s.start, 0, 0, n);
    const stop = clamp(s.stop, n, 0, n);
    for (let i = start; i < stop; i += step) out.push(i);
  } else {
    const start = clamp(s.start, n - 1, -1, n - 1);
    const stop = clamp(s.stop, -1, -1, n - 1);
    for (let i = start; i > stop; i += step) out.push(i);
  }
  return out;
}

/** The class names of a value (SymPy `type(expr).mro()`). */
function typeNames(v: unknown): Set<string> {
  const names = new Set<string>();
  if (v instanceof Expr) {
    names.add(sympyClassName(v));
    for (const b of sympyClassBases(v)) names.add(b);
  } else if (Array.isArray(v)) {
    // a Python tuple or list
    names.add('tuple');
    names.add('list');
  } else if (typeof v === 'number') names.add(Number.isInteger(v) ? 'int' : 'float');
  else if (typeof v === 'bigint') names.add('int');
  else if (typeof v === 'string') names.add('str');
  else if (typeof v === 'boolean') names.add('bool');
  // other objects match the JavaScript names of their classes
  for (let p: unknown = typeof v === 'object' && v !== null && !(v instanceof Expr) ? Object.getPrototypeOf(v) : null; typeof p === 'object' && p !== null; p = Object.getPrototypeOf(p)) {
    const ctor: unknown = Reflect.get(p, 'constructor');
    if (typeof ctor === 'function' && ctor.name) names.add(ctor.name);
  }
  return names;
}

const camel = (n: string): string => n.replace(/_([a-z0-9])/g, (_m, ch: string) => ch.toUpperCase());

/** Python hasattr(): `__iter__` is iterability, `is_*` flags exist on expressions, other names are properties (also in camelCase). */
function hasAttr(v: unknown, attr: string): boolean {
  if (attr === '__iter__') return typeof v === 'string' || (typeof v === 'object' && v !== null && Symbol.iterator in v);
  if (typeof v !== 'object' || v === null) return false;
  // every SymPy Basic object has the is_* flags
  if (v instanceof Expr && attr.startsWith('is_')) return true;
  return attr in v || camel(attr) in v;
}

/** The arguments of an expression in printing order (SymPy EPath._get_ordered_args). */
function orderedArgs(e: Expr): readonly Expr[] {
  if (e instanceof Add) return asOrderedTerms(e);
  if (e instanceof Mul) return asOrderedFactors(e);
  return sympyArgs(e);
}

/**
 * SymPy EPath: a compiled path selecting parts of an expression or of
 * nested arrays (Python tuples and lists).
 *
 * ```text
 * literal   ::= /[A-Za-z_][A-Za-z_0-9]*\/
 * number    ::= /-?\d+/
 * type      ::= literal
 * attribute ::= literal "?"
 * all       ::= "*"
 * slice     ::= "[" number? (":" number? (":" number?)?)? "]"
 * range     ::= all | slice
 * query     ::= (type | attribute) ("|" (type | attribute))*
 * selector  ::= range | query range?
 * path      ::= "/" selector ("/" selector)*
 * ```
 *
 * Types are SymPy class names (and their superclasses: `Symbol`, `Number`,
 * `Function`, ...), `int`, `float`, `str` and `tuple`/`list` for arrays;
 * `__iter__?` tests that a value is iterable.
 */
export class EPath {
  readonly #path: string;
  readonly #epath: readonly Selector[];

  /** Compile a path (an EPath is returned as it is by {@link epath}). */
  constructor(path: string | EPath) {
    if (path instanceof EPath) {
      this.#path = path.#path;
      this.#epath = path.#epath;
      return;
    }
    if (!path) throw new RangeError('empty EPath');
    if (!path.startsWith('/')) throw new NotImplementedError('non-root EPath');
    this.#path = path;
    this.#epath = path.slice(1).split('/').map(compileSelector);
  }

  /** The path string. */
  get path(): string {
    return this.#path;
  }

  /** SymPy repr: `EPath('/*\/[0]')`. */
  toString(): string {
    return `EPath('${this.#path}')`;
  }

  #has(v: unknown, sel: Selector): boolean {
    const { attrs, types } = sel;
    if (!attrs.length && !types.length) return true;
    if (attrs.length && attrs.every((a) => hasAttr(v, a))) return true;
    if (types.length) {
      const names = typeNames(v);
      return types.some((t) => names.has(t));
    }
    return false;
  }

  /**
   * Apply func (with the extra arguments args) to the parts of expr selected
   * by the path; the rest of expr is rebuilt around the results.
   */
  apply<P = Expr>(expr: unknown, func: EPathFunction<P>, args: readonly unknown[] = []): unknown {
    // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the selected parts are what the caller's path selects; their type is the caller's claim, as in SymPy
    const f = func as (part: unknown, ...a: readonly unknown[]) => unknown;
    const go = (path: readonly Selector[], e: unknown): unknown => {
      const [sel, ...rest] = path;
      if (sel === undefined) return f(e, ...args);
      let items: unknown[];
      if (e instanceof Expr) {
        if (isSympyAtom(e)) return e;
        items = [...orderedArgs(e)];
      } else if (Array.isArray(e)) items = [...(e as readonly unknown[])];
      else return e;
      const { span } = sel;
      const indices = span === null ? items.map((_x, i) => i) : typeof span === 'number' ? [span] : sliceIndices(span, items.length);
      for (const i0 of indices) {
        const i = i0 < 0 ? i0 + items.length : i0;
        if (i < 0 || i >= items.length) continue;
        if (this.#has(items[i], sel)) items[i] = go(rest, items[i]);
      }
      if (e instanceof Expr) return sympyRebuild(e, items.map((x) => toExpr(x)));
      return items;
    };
    return go(this.#epath, expr);
  }

  /** The parts of expr selected by the path. */
  select(expr: unknown): unknown[] {
    const result: unknown[] = [];
    const go = (path: readonly Selector[], e: unknown): void => {
      const [sel, ...rest] = path;
      if (sel === undefined) {
        result.push(e);
        return;
      }
      let items: readonly unknown[];
      if (e instanceof Expr) items = orderedArgs(e);
      else if (Array.isArray(e)) items = e as readonly unknown[];
      else return;
      const { span } = sel;
      if (span !== null) {
        if (typeof span === 'number') {
          const i = span < 0 ? span + items.length : span;
          if (i < 0 || i >= items.length) return;
          items = [items[i]];
        } else items = sliceIndices(span, items.length).map((i) => items[i]);
      }
      for (const x of items) if (this.#has(x, sel)) go(rest, x);
    };
    go(this.#epath, expr);
    return result;
  }
}

/**
 * SymPy `epath(path, expr=None, func=None, args=None)`: without expr, the
 * compiled {@link EPath}; without func, the parts of expr selected by the
 * path; otherwise expr with func (called with the part and the extra
 * arguments args) applied to each selected part. The path syntax:
 *
 * - `/*` selects all arguments (or items of an array);
 * - `/[0]`, `/[1:5]`, `/[1:5:2]` select by index or slice;
 * - `/Symbol`, `/int|tuple` select by type (SymPy class names, `int`,
 *   `float`, `str`, and `tuple` or `list` for arrays);
 * - `/__iter__?` selects by attribute (iterable values; other names are
 *   properties, also in camelCase).
 *
 * The arguments of sums and products are taken in printing order.
 */
export function epath(path: string | EPath): EPath;
export function epath(path: string | EPath, expr: unknown): unknown[];
export function epath<P = Expr>(path: string | EPath, expr: unknown, func: EPathFunction<P>, args?: readonly unknown[]): unknown;
export function epath<P = Expr>(path: string | EPath, ...rest: [] | [unknown] | [unknown, EPathFunction<P>, (readonly unknown[])?]): unknown {
  const p = new EPath(path);
  if (!rest.length) return p;
  const [expr, func, args] = rest;
  return func === undefined ? p.select(expr) : p.apply(expr, func, args);
}
