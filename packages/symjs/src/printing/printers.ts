// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Parts ported from SymPy (sympy/printing/str.py and latex.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file The printer entry points of SymPy around `str` and `latex`: the
 * `StrPrinter` class, `sstr`, `sstrrepr`, `print_latex` and `multiline_latex`.
 */

import type { FracElement, GaussianIntegerRing, GaussianRationalField, PolyElement } from '../polys';
import type { Predicate } from '../core/refine';
import type { ExprLike } from '../core/nodes';
import { Expr, ExtensionExpr, isNum } from '../core/nodes';
import { mul, sympify } from '../core/ops';
import { at, first } from '../core/guard';
import { isNoMatch, type NoMatchResult } from '../core/truth';
import { str, withFullPrec, withPermCyclic } from './str';
import { latex } from './latex';
import type { LatexOptions, LatexPrintable } from './latex';
import { asOrderedFactors, asOrderedTerms, compareKeys, sortKey } from './sortkey';

/** A matrix supplied by a higher layer, with entries printed by the str printer. */
interface StrMatrix {
  readonly rows: number;
  readonly cols: number;
  get(i: number, j: number): Expr;
}

/** A value the str printers accept, including matrices and native containers. */
interface FrozenSetItems {
  readonly frozenItems: ReadonlySet<StrPrintable>;
}

/** A value accepted by the plain-text expression printer. */
export type StrPrintable = FrozenSetItems | Predicate | { asExpr(): Expr; toString(): string } | StrMatrix | ExprLike | string | boolean | null | NoMatchResult | readonly StrPrintable[] | ReadonlySet<StrPrintable> | ReadonlyMap<StrPrintable, StrPrintable> | PrintableObject;
/** Any other object printed by its own `toString` (permutations, cycles, domain matrices, groups, ...). */
export interface PrintableObject {
  toString(): string;
}

/** Python's repr of a string ('abc', or "it's" when it contains a single quote). */
function reprString(s: string): string {
  if (s.includes("'") && !s.includes('"')) return `"${s}"`;
  return `'${s.replace(/\\/g, '\\\\').replace(/'/g, "\\'").replace(/\n/g, '\\n')}'`;
}

const isExprLike = (x: StrPrintable): x is ExprLike => x instanceof Expr || typeof x === 'number' || typeof x === 'bigint';
const isMap = (x: StrPrintable): x is ReadonlyMap<StrPrintable, StrPrintable> => x instanceof Map;
const isSet = (x: StrPrintable): x is ReadonlySet<StrPrintable> => x instanceof Set;

const isMatrix = (v: object): v is StrMatrix => 'rows' in v && 'cols' in v && 'get' in v && typeof v.get === 'function';

const isPolyElement = (v: object): v is PolyElement => 'listterms' in v && 'ring' in v;
const isFracElement = (v: object): v is FracElement => 'numer' in v && 'denom' in v && 'field' in v;
const isGaussian = (v: object): v is GaussianIntegerRing | GaussianRationalField => 'imagUnit' in v;

function polynomialString(poly: PolyElement): string {
  const domain = poly.ring.domain;
  if (!isGaussian(domain)) return String(poly);
  return poly.terms().map(([powers, coeff]) => {
    const monomial = powers.flatMap((n, j) => n === 0 ? [] : [str(at(poly.ring.symbols, j)) + (n === 1 ? '' : `**${n}`)]).join('*');
    if (monomial && coeff.equals(1)) return monomial;
    const c = domain.convert(coeff);
    const factor = `(${c.re.toString()} + ${c.im.toString()}*I)`;
    return monomial ? factor + '*' + monomial : factor;
  }).join(' + ') || '(0 + 0*I)';
}

function printValue(v: StrPrintable, strings: (s: string) => string): string {
  const go = (x: StrPrintable): string => printValue(x, strings);
  if (v instanceof ExtensionExpr && v.name === 'Str' && strings === reprString) return `Str(${strings(str(v))})`;
  if (isExprLike(v)) return str(sympify(v));
  if (v === null) return 'None';
  if (typeof v === 'boolean') return v ? 'True' : 'False';
  if (typeof v === 'string') return strings(v);
  if ('predicateName' in v) return String(v);
  if (isMatrix(v)) {
    if (v.rows === 0 || v.cols === 0) return `Matrix(${v.rows}, ${v.cols}, [])`;
    const rows = Array.from({ length: v.rows }, (_, i) => Array.from({ length: v.cols }, (_, j) => go(v.get(i, j))));
    const widths = Array.from({ length: v.cols }, (_, j) => Math.max(...rows.map((r) => at(r, j).length)));
    const lines = rows.map((r) => `[${r.map((s, j) => s.padStart(at(widths, j))).join(', ')}]`);
    return `Matrix([${v.rows === 1 ? '' : '\n'}${lines.join(',\n')}])`;
  }
  if (isMap(v)) return `{${[...v].map(([k, x]) => `${go(k)}: ${go(x)}`).join(', ')}}`;
  if (isSet(v)) {
    const items = [...v];
    if (items.every((x) => isExprLike(x))) items.sort((a, b) => compareKeys(sortKey(sympify(a)), sortKey(sympify(b))));
    return items.length ? `{${items.map(go).join(', ')}}` : 'set()';
  }
  if ('frozenItems' in v) return `frozenset(${v.frozenItems.size ? go(v.frozenItems) : ''})`;
  if (isPolyElement(v)) return polynomialString(v);
  if (isFracElement(v)) {
    const n = polynomialString(v.numer);
    if (v.denom.equals(1)) return n;
    const d = polynomialString(v.denom);
    return (v.numer.length > 1 ? `(${n})` : n) + '/' + (v.denom.isGenerator || v.denom.isGround ? d : `(${d})`);
  }
  if ('asExpr' in v) return String(v);
  if (isList(v)) return `[${v.map(go).join(', ')}]`;
  // NoMatch is SymPy's None
  if (isNoMatch(v)) return 'None';
  if (v.toString === Object.prototype.toString) throw new TypeError(`sstr: cannot print ${String(v.constructor.name)}`);
  return v.toString();
}

const isList = (v: object): v is readonly StrPrintable[] => Array.isArray(v);

/**
 * Formats expressions and containers in plain text. Nested containers retain their list, set or dictionary notation.
 *
 * @see SymPy `sympy.printing.str.StrPrinter`
 */
export class StrPrinter {
  /**
   * Creates a StrPrinter instance.
   *
   * @param settings - The settings for constructor.
   */
  constructor(
    /** The formatting settings for this printer. */
    readonly settings: Readonly<Record<string, unknown>> = {}) {}
  /**
   * The str form of expr.
   *
   * @param expr - The value to format.
   * @returns The formatted text.
   * @see SymPy `sympy.printing.str.StrPrinter.doprint`
   */
  doprint(expr: StrPrintable): string {
    return sstr(expr, this.settings);
  }
  /**
   * SymPy's fallback printer for strings, expressions and scalar values.
   *
   * @param expr - The value to format.
   * @returns The formatted text.
   * @see SymPy `sympy.printing.str.StrPrinter.emptyPrinter`
   */
  emptyPrinter(expr: StrPrintable): string {
    return printValue(expr, (s) => s);
  }
}

/** The settings of {@link sstr}. */
export interface SstrOptions {
  /**
   * Prints floats with their full precision (true), with trailing zeros
   * removed (false), or with the full precision only at the top level
   * ('auto', the default; SymPy full_prec).
   */
  fullPrec?: boolean | 'auto';
  /** Uses explicit integer constructors in the printed representation. */
  sympyIntegers?: boolean;
  /** The lower exponent threshold for scientific notation. */
  min?: number;
  /** The upper exponent threshold for scientific notation. */
  max?: number;
  /** The number of decimal digits to print. */
  dps?: number;
  /** Permutations in cycle notation (default true) or as Permutation([...]). */
  permCyclic?: boolean;
}

/**
 * The str form of an expression or a container of them
 * (lists, sets, dicts, strings and None print as Python prints them inside
 * a container).
 *
 * @param expr - The value to format.
 * @param opts - The sstr settings.
 * @returns The plain-text representation.
 * @see SymPy `sympy.printing.str.sstr`
 * @example
 * ```ts
 * import { ex, sstr } from '@symjs/symjs';
 * sstr(ex`x**2 + 1`); // => x**2 + 1
 * ```
 */
export function sstr(expr: StrPrintable, opts: SstrOptions = {}): string {
  for (const key of Object.keys(opts)) if (!['fullPrec', 'permCyclic', 'order', 'sympyIntegers', 'abbrev', 'min', 'max', 'dps'].includes(key)) throw new TypeError(`Unknown setting '${key}'.`);
  return withPermCyclic(opts.permCyclic, () => withFullPrec(opts, () => printValue(expr, (s) => s)));
}

/**
 * Like sstr, but strings are printed with their quotes (Python repr).
 *
 * @param expr - The value to format.
 * @returns The plain-text representation.
 * @see SymPy `sympy.printing.str.sstrrepr`
 */
export function sstrrepr(expr: StrPrintable): string {
  return printValue(expr, reprString);
}

/**
 * Prints LaTeX representation of the given expression. Takes the same settings as ``latex()``.
 *
 * @param expr - The value to format.
 * @param options - The latex settings.
 * @returns The formatted LaTeX source.
 * @see SymPy `sympy.printing.latex.print_latex`
 */
export function printLatex(expr: LatexPrintable, options?: LatexOptions): string {
  return `${latex(expr, options)}\n`;
}

/** The options of {@link multilineLatex}: its own and the settings of the LaTeX printer. */
export interface MultilineLatexOptions extends LatexOptions {
  /** Terms per line (default 1). */
  termsPerLine?: number;
  /** 'align*' (default), 'eqnarray' or 'IEEEeqnarray'. */
  environment?: 'align*' | 'eqnarray' | 'IEEEeqnarray';
  /** End each broken line with \dots. */
  useDots?: boolean;
}

/**
 * Lhs = rhs with the terms of rhs over several lines of a
 * LaTeX align* (or eqnarray, IEEEeqnarray) environment.
 *
 * @remarks SymPy returns `\begin{align*} x = & e^{i \alpha} \\ & + \sin{\left(\alpha y \right)} \\ & - \cos{\left(\log{\left(y \right)} \right)}  \end{align*}`.
 *
 * @param lhs - The left side of the equation.
 * @param rhs - The right side whose terms are split across lines.
 * @param termsOrOptions - The number of terms per line or the multiline formatting settings.
 * @returns The formatted LaTeX source.
 * @see SymPy `sympy.printing.latex.multiline_latex`
 * @example
 * ```ts
 * import { ex, multilineLatex } from '@symjs/symjs';
 * multilineLatex(ex`x`, ex`exp(I*alpha) + sin(alpha*y) - cos(log(y))`); // => \begin{align*}
 * //   x = & e^{i \alpha} \\
 * //   & + \sin{\left(\alpha y \right)} \\
 * //   & - \cos{\left(\log{\left(y \right)} \right)}
 * //   \end{align*}
 * ```
 */
export function multilineLatex(lhs: ExprLike, rhs: ExprLike, termsOrOptions: number | MultilineLatexOptions = {}): string {
  // SymPy's third positional parameter is terms_per_line
  const options = typeof termsOrOptions === 'number' ? { termsPerLine: termsOrOptions } : termsOrOptions;
  const { termsPerLine = 1, environment = 'align*', useDots = false, ...settings } = options;
  const tex = (e: ExprLike): string => latex(sympify(e), settings);
  const env = {
    eqnarray: { begin: '\\begin{eqnarray}\n', first: '& = &', nonumber: '\\nonumber', end: '\n\\end{eqnarray}', doubleet: true },
    IEEEeqnarray: { begin: '\\begin{IEEEeqnarray}{rCl}\n', first: '& = &', nonumber: '\\nonumber', end: '\n\\end{IEEEeqnarray}', doubleet: true },
    'align*': { begin: '\\begin{align*}\n', first: '= &', nonumber: '', end: '\n\\end{align*}', doubleet: false },
  }[environment];
  const dots = useDots ? '\\dots' : '';
  const terms = asOrderedTerms(sympify(rhs));
  let result = env.begin;
  let count = 1;
  terms.forEach((t0, i) => {
    let term = t0;
    let start = '';
    let end = '';
    let sign = '+';
    if (count > termsPerLine) {
      start = env.doubleet ? '& & ' : '& ';
      count = 1;
    }
    if (count === termsPerLine && i < terms.length - 1) end = `${dots}${env.nonumber}\\\\\n`;
    // SymPy Mul.as_ordered_factors splits a negative coefficient c into -1 and -c
    const c = first(asOrderedFactors(term));
    if (isNum(c) && c.isNegative) {
      term = mul(-1, term);
      sign = '-';
    }
    if (i === 0) result += `${tex(lhs)} ${env.first}${sign === '+' ? '' : sign} ${tex(term)} ${end}`;
    else result += `${start}${sign} ${tex(term)} ${end}`;
    count++;
  });
  return result + env.end;
}
