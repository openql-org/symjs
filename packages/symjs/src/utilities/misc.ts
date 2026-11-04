// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/utilities/misc.py) and Python's textwrap, BSD-3-Clause / PSF.

/**
 * @file Text helpers of SymPy's `sympy.utilities.misc`: `filldedent` and the
 * `textwrap` functions it uses (`dedent`, `fill`).
 */

import { at, last } from '../core/guard';

/** Python textwrap.dedent: the common leading whitespace removed from every line (blank lines become empty). */
export function dedent(text: string): string {
  const lines = text.split('\n').map((l) => (/^[ \t]+$/.test(l) ? '' : l));
  let margin: string | undefined;
  for (const l of lines) {
    if (!l) continue;
    // a line that is not blank has a character other than a space or tab
    const indent = l.slice(0, l.search(/[^ \t]/));
    if (margin === undefined) margin = indent;
    else {
      let k = 0;
      while (k < margin.length && k < indent.length && margin[k] === indent[k]) k++;
      margin = margin.slice(0, k);
    }
  }
  const m = margin ?? '';
  return lines.map((l) => (l.startsWith(m) ? l.slice(m.length) : l)).join('\n');
}

/**
 * Python textwrap.fill(text, width): text (each whitespace character a
 * space) cut into words, whitespace runs and hyphenated parts, filled
 * greedily on lines of at most `width` characters; whitespace at a line
 * break is dropped and a word longer than a line is broken.
 */
export function fill(text: string, width = 70): string {
  if (width < 1) throw new RangeError(`invalid width ${width} (must be > 0)`);
  const chunks = text.replace(/\s/g, ' ').match(/ +|\S*?\w-(?=\w)|\S+/g) ?? [];
  const blank = (c: string): boolean => c.trim() === '';
  const lines: string[] = [];
  let i = 0;
  while (i < chunks.length) {
    // whitespace at the start of a line (but the first) is dropped
    if (lines.length && blank(at(chunks, i))) i++;
    const cur: string[] = [];
    let len = 0;
    while (i < chunks.length && len + at(chunks, i).length <= width) {
      const c = at(chunks, i++);
      cur.push(c);
      len += c.length;
    }
    const next = chunks[i];
    if (next !== undefined && next.length > width) {
      // break_long_words: as much of the word as fits (Python's _handle_long_word)
      const room = width - len;
      cur.push(next.slice(0, room));
      chunks[i] = next.slice(room);
    }
    if (cur.length && blank(last(cur))) cur.pop();
    if (cur.length) lines.push(cur.join(''));
  }
  return lines.join('\n');
}

/**
 * SymPy filldedent(s, w=70): s dedented, stripped of leading and trailing
 * newlines and refilled to width w, after a leading newline.
 */
export function filldedent(s: string, w = 70): string {
  return `\n${fill(dedent(s).replace(/^\n+|\n+$/g, ''), w)}`;
}
