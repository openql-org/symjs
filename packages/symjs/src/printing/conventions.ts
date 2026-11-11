// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/printing/conventions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file The conventions shared by the printers (SymPy
 * sympy.printing.conventions): how a symbol name is split into its name,
 * superscripts and subscripts.
 */

/**
 * SymPy `split_super_sub(text)`: the name, the superscripts and the
 * subscripts of a symbol name. A superscript starts with `^` or `__`, a
 * subscript with `_`; a name that ends with digits has them as its first
 * subscript (`x2` is `x` with subscript `2`).
 *
 * `splitSuperSub('a_x^1')` is `['a', ['1'], ['x']]`.
 */
export function splitSuperSub(text: string): [string, string[], string[]] {
  if (text.length === 0) return [text, [], []];
  const supers: string[] = [];
  const subs: string[] = [];
  // the end of the part starting at pos: the next ^ or _ after its first character (or a leading __)
  const partEnd = (pos: number): number => {
    let start = pos + 1;
    if (text.slice(pos, pos + 2) === '__') start += 1;
    let posHat = text.indexOf('^', start);
    if (posHat < 0) posHat = text.length;
    let posUsc = text.indexOf('_', start);
    if (posUsc < 0) posUsc = text.length;
    return Math.min(posHat, posUsc);
  };
  let pos = partEnd(0);
  let name = text.slice(0, pos);
  while (pos < text.length) {
    const next = partEnd(pos);
    const part = text.slice(pos, next);
    pos = next;
    // every part after the name starts with ^, __ or _
    if (part.startsWith('^')) supers.push(part.slice(1));
    else if (part.startsWith('__')) supers.push(part.slice(2));
    else subs.push(part.slice(1));
  }
  // a name ending with digits: the digits are a subscript (Python's [^\W\d_]+ then \d+)
  const m = /^([\p{L}\p{M}\p{Nl}\p{No}]+)(\p{Nd}+)$/u.exec(name);
  if (m?.[1] !== undefined && m[2] !== undefined) {
    name = m[1];
    subs.unshift(m[2]);
  }
  return [name, supers, subs];
}
