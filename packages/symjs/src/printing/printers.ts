// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Parts ported from SymPy (sympy/printing/str.py and latex.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file The printer entry points of SymPy around `str` and `latex`: the
 * `StrPrinter` class, `sstr`, `sstrrepr`, `print_latex` and `multiline_latex`.
 */

import type { ExprLike } from '../core/nodes';
import { Expr, isNum } from '../core/nodes';
import { mul, sympify } from '../core/ops';
import { first } from '../core/guard';
import { str, withFullPrec } from './str';
import { latex } from './latex';
import type { LatexOptions, LatexPrintable } from './latex';
import { asOrderedFactors, asOrderedTerms } from './sortkey';

/** A value the str printers accept: an expression, a number, a string, or a list, tuple, set or dict of them. */
export type StrPrintable = ExprLike | string | boolean | null | readonly StrPrintable[] | ReadonlySet<StrPrintable> | ReadonlyMap<StrPrintable, StrPrintable>;

/** Python's repr of a string ('abc', or "it's" when it contains a single quote). */
function reprString(s: string): string {
  if (s.includes("'") && !s.includes('"')) return `"${s}"`;
  return `'${s.replace(/\\/g, '\\\\').replace(/'/g, "\\'").replace(/\n/g, '\\n')}'`;
}

const isExprLike = (x: StrPrintable): x is ExprLike => x instanceof Expr || typeof x === 'number' || typeof x === 'bigint';
const isMap = (x: StrPrintable): x is ReadonlyMap<StrPrintable, StrPrintable> => x instanceof Map;
const isSet = (x: StrPrintable): x is ReadonlySet<StrPrintable> => x instanceof Set;

function printValue(v: StrPrintable, strings: (s: string) => string): string {
  const go = (x: StrPrintable): string => printValue(x, strings);
  if (isExprLike(v)) return str(sympify(v));
  if (v === null) return 'None';
  if (typeof v === 'boolean') return v ? 'True' : 'False';
  if (typeof v === 'string') return strings(v);
  if (isMap(v)) return `{${[...v].map(([k, x]) => `${go(k)}: ${go(x)}`).join(', ')}}`;
  if (isSet(v)) return v.size ? `{${[...v].map(go).join(', ')}}` : 'set()';
  return `[${v.map(go).join(', ')}]`;
}

/**
 * SymPy StrPrinter: `new StrPrinter().doprint(expr)` is `str(expr)`; lists,
 * sets, dicts, strings and None print as Python prints them inside a
 * container.
 */
export class StrPrinter {
  constructor(readonly settings: Readonly<Record<string, unknown>> = {}) {}
  /** The str form of expr (SymPy StrPrinter.doprint). */
  doprint(expr: StrPrintable): string {
    return printValue(expr, (s) => s);
  }
}

/** The settings of {@link sstr}. */
export interface SstrOptions {
  /**
   * Print floats with their full precision (true), with trailing zeros
   * removed (false), or with the full precision only at the top level
   * ('auto', the default; SymPy full_prec).
   */
  fullPrec?: boolean | 'auto';
}

/**
 * SymPy sstr: the str form of an expression or a container of them
 * (lists, sets, dicts, strings and None print as Python prints them inside
 * a container).
 */
export function sstr(expr: StrPrintable, opts: SstrOptions = {}): string {
  return withFullPrec(opts.fullPrec ?? 'auto', () => printValue(expr, (s) => s));
}

/** SymPy sstrrepr: like sstr, but strings are printed with their quotes (Python repr). */
export function sstrrepr(expr: StrPrintable): string {
  return printValue(expr, reprString);
}

/**
 * SymPy print_latex(expr): SymPy prints the LaTeX form; symjs has no console
 * output, so this returns the text that would be printed (followed by a
 * newline).
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
 * SymPy multiline_latex(lhs, rhs, terms_per_line=1, environment="align*",
 * use_dots=False): lhs = rhs with the terms of rhs over several lines of a
 * LaTeX align* (or eqnarray, IEEEeqnarray) environment.
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
