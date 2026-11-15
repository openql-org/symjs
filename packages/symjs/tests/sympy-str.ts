// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Prints a result like Python's `str()` of the SymPy result, for the tests generated from
 * SymPy's doctests and unit tests (`*.corpus.test.ts`).
 *
 * Expressions print with symjs's `str`. A JS array stands for a Python list or tuple: `brackets`
 * gives the kind of each array in preorder (`l` list, `t` tuple; arrays beyond it are lists). A
 * `Map` is a dict, a `Set` a set, `true`/`false` print as `True`/`False`, and the absent results
 * (`'unknown'`, `NoMatch`, `Unsolved`, `null`) as `None`.
 */

import * as sj from '../src';

/** Items of containers print by their repr where it differs from their str. */
function item(v: unknown, kinds: Kinds): string {
  if (v instanceof sj.Permutation) return sj.permutationRepr(v);
  if (v instanceof sj.TransitiveSubgroup || v instanceof sj.PrimeIdeal) return v.repr();
  if (v instanceof sj.PythonMPQ || v instanceof sj.GaussianElement || v instanceof sj.ModularInteger || v instanceof sj.ANP) return v.repr();
  if (v instanceof sj.DDM || v instanceof sj.SDM) return v.repr();
  return format(v, kinds);
}

class Kinds {
  private next = 0;
  constructor(private readonly kinds: string) {}
  take(): string {
    return this.kinds[this.next++] ?? 'l';
  }
}

const symbolName = (s: sj.Expr | undefined): string => (s === undefined ? '' : sj.str(s));

function algebraicPolyElement(v: sj.PolyElement, K: sj.AlgebraicField): string {
  // SymPy prints sparse algebraic coefficients in their ANP representation.
  const terms = v.terms().map(([m, c], i) => {
    const negative = K.isNegative(K.convert(c));
    const monomial = m.flatMap((n, j) => (n === 0 ? [] : [symbolName(v.ring.symbols[j]) + (n === 1 ? '' : `**${n}`)])).join('*');
    const coeff = K.convert(negative && monomial ? sj.neg(c) : c);
    const factor = monomial && coeff.equals(K.one) ? '' : coeff.repr();
    return (i === 0 ? (negative ? '-' : '') : negative ? ' - ' : ' + ') + factor + (factor && monomial ? '*' : '') + monomial;
  });
  return terms.join('') || K.convert(0).repr();
}

function format(v: unknown, kinds: Kinds): string {
  if (v instanceof sj.PolyElement && v.ring.domain instanceof sj.AlgebraicField) return algebraicPolyElement(v, v.ring.domain);
  if (v instanceof sj.Expr) return sj.str(v);
  if (v instanceof sj.AlgebraicNumber) return sj.str(v.asExpr());
  if (v === 'unknown' || v === null || v === undefined || sj.isNoMatch(v) || sj.isUnsolved(v)) return 'None';
  if (v instanceof Error) return v.message;
  if (Array.isArray(v)) {
    const isList = kinds.take() === 'l';
    const items = v.map((x: unknown) => item(x, kinds));
    if (isList) return `[${items.join(', ')}]`;
    return items.length === 1 ? `(${items[0]},)` : `(${items.join(', ')})`;
  }
  if (v instanceof Map) return `{${[...v].map(([k, x]) => `${item(k, kinds)}: ${item(x, kinds)}`).join(', ')}}`;
  if (v instanceof Set) return v.size === 0 ? 'set()' : `{${[...v].map((x) => item(x, kinds)).join(', ')}}`;
  if (v === -Infinity) return '-oo';
  if (typeof v === 'boolean') return v ? 'True' : 'False';
  if (typeof v === 'number' || typeof v === 'bigint') return String(v);
  if (typeof v === 'string') return v.includes("'") && !v.includes('"') ? `"${v}"` : `'${v}'`;
  // a function class (expm1, isnan) prints its name, an unapplied predicate (Q.even) its str
  if (typeof v === 'function') {
    const name: unknown = Reflect.get(v, 'functionName');
    if (typeof name === 'string') return name;
    if (typeof Reflect.get(v, 'predicateName') === 'string') return String(v);
  }
  // library objects with their own SymPy-like str (Matrix, Poly, Cycle, DomainMatrix, ...)
  if (typeof v === 'object') {
    const f: unknown = Reflect.get(v, 'toString');
    if (typeof f === 'function' && f !== Object.prototype.toString) {
      const s: unknown = Reflect.apply(f, v, []);
      if (typeof s === 'string') return s;
    }
  }
  throw new TypeError(`sympyStr: no SymPy form for ${Object.prototype.toString.call(v)}`);
}

export function sympyStr(v: unknown, brackets = ''): string {
  return format(v, new Kinds(brackets));
}

/** The item of a result at an index (a generated test indexes results the way SymPy's tests do). */
export function at<T>(items: readonly T[], index: number): T {
  const v = items[index];
  if (v === undefined) throw new RangeError(`at: no item ${index}`);
  return v;
}

/** Python's str() of a result: a string is itself, anything else prints like sympyStr. */
export function pyStr(v: unknown, brackets = ''): string {
  return typeof v === 'string' ? v : sympyStr(v, brackets);
}

/** Python's repr() of a result (strings quoted, domain elements by their repr). */
export function pyRepr(v: unknown, brackets = ''): string {
  return item(v, new Kinds(brackets));
}

/** The items Python iterates in a result (list(...), tuple(...), len(...)). */
export function pyItems(v: unknown): unknown[] {
  if (typeof v === 'string') return Array.from(v);
  if (v instanceof Map) return [...v.keys()];
  if (typeof v === 'object' && v !== null && Symbol.iterator in v) return [...(v as Iterable<unknown>)];
  throw new TypeError(`pyItems: ${Object.prototype.toString.call(v)} is not iterable`);
}

/** Python's len() of a result. */
export function pyLen(v: unknown): number {
  if (typeof v === 'string' || Array.isArray(v)) return v.length;
  if (v instanceof Map || v instanceof Set) return v.size;
  if (typeof v === 'object' && v !== null && !(Symbol.iterator in v)) {
    const n: unknown = Reflect.get(v, 'length');
    if (typeof n === 'number') return n;
  }
  return pyItems(v).length;
}

/** The str() of each item of a result ([str(r) for r in result]). */
export function strItems(v: unknown): string[] {
  return pyItems(v).map((x) => pyStr(x));
}

/** Printed text as SymPy's doctest runner compares it: trailing newlines dropped, whitespace normalized on request. */
export function text(s: string, normalizeWhitespace = false): string {
  return normalizeWhitespace ? s.replace(/\s+/g, ' ').trim() : s.replace(/\n+$/, '');
}

function topLevelItems(s: string): string[] {
  const out: string[] = [];
  let depth = 0;
  let cur = '';
  for (const ch of s.slice(1, -1)) {
    if ('([{'.includes(ch)) depth++;
    if (')]}'.includes(ch)) depth--;
    if (ch === ',' && depth === 0) {
      out.push(cur.trim());
      cur = '';
    } else cur += ch;
  }
  if (cur.trim()) out.push(cur.trim());
  return out;
}

/** Set and dict literals at any depth with their items sorted (Python prints them in hash order). */
function normalizeSets(s: string): string {
  let out = '';
  let i = 0;
  while (i < s.length) {
    if (s[i] !== '{') {
      out += s[i];
      i++;
      continue;
    }
    let depth = 0;
    let j = i;
    for (; j < s.length; j++) {
      if ('([{'.includes(s.charAt(j))) depth++;
      if (')]}'.includes(s.charAt(j))) depth--;
      if (depth === 0) break;
    }
    out += `{${topLevelItems(s.slice(i, j + 1)).map(normalizeSets).sort().join(', ')}}`;
    i = j + 1;
  }
  return out;
}

/** QQ elements of SymPy's pure Python ground types print as MPQ(p,q). */
const unMPQ = (s: string): string => s.replace(/MPQ\((-?\d+),(\d+)\)/g, (_m, p: string, q: string) => (q === '1' ? p : `${p}/${q}`));
/** Spacing at delimiters, outside quoted strings (SymPy lays out nested matrix reprs on several lines). */
const normalizeLayout = (s: string): string => s.replace(/'(?:\\.|[^'\\])*'|"(?:\\.|[^"\\])*"|[^'"]+/g, (part) => (/^["']/.test(part) ? part : part.replace(/\s*([()[\]{},])\s*/g, '$1')));
/** A Python tuple and list of the same items agree (JavaScript has only arrays). */
const asList = (t: string): string => t.replace(/,\)/g, ')').replace(/\(/g, '[').replace(/\)/g, ']');

/**
 * The result agrees with SymPy's printed result: the same str(), or the same up to the order of set
 * and dict items, the layout of nested reprs, list or tuple brackets, and MPQ notation.
 */
export function sympyMatches(v: unknown, expected0: string, brackets = ''): boolean {
  const expected = expected0.includes('MPQ(') ? unMPQ(expected0) : expected0;
  const got = expected0.includes('MPQ(') ? unMPQ(sympyStr(v, brackets)) : sympyStr(v, brackets);
  if (got === expected || (expected === 'Interval(-oo, oo)' && got === 'Reals')) return true;
  if (normalizeLayout(got) === normalizeLayout(expected)) return true;
  if (v instanceof sj.GroebnerBasis && expected.startsWith('[')) return sympyMatches([...v.exprs], expected, 'l');
  if (v === -Infinity && expected === '-inf') return true;
  if (got.includes('{') && normalizeSets(got) === normalizeSets(expected)) return true;
  for (const prefix of ["defaultdict(<class 'list'>, ", "defaultdict(<class 'set'>, ", "defaultdict(<class 'int'>, "]) {
    if (expected.startsWith(prefix)) return sympyMatches(v, expected.slice(prefix.length, -1), brackets);
  }
  if ((v instanceof Map || v instanceof Set) && expected.startsWith('{')) {
    const a = topLevelItems(got).sort();
    const b = topLevelItems(expected).sort();
    return a.length === b.length && a.every((x, i) => x === b[i]);
  }
  if (Array.isArray(v)) return asList(got) === asList(expected) || normalizeSets(asList(got)) === normalizeSets(asList(expected));
  return false;
}
