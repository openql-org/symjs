// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/utilities/misc.py) and Python's textwrap, BSD-3-Clause / PSF.

/**
 * @file The helpers of SymPy's `sympy.utilities.misc`: `filldedent` and the
 * `textwrap` functions it uses (`dedent`, `fill`), the source-text helpers
 * `rawlines` and `strlines`, the string substitutions `translate` and
 * `replace` (exported as `replaceString`, `replace` being the expression
 * operation), `asInt` and `funcName`.
 */

import { at, getOrThrow, last } from '../core/guard';
import { translateSymbol } from '../printing/latex';
import { Expr, Float, Rational } from '../core/nodes';
import { funcName as nodeClassName } from '../strategies/util';

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
 * S dedented, stripped of leading and trailing
 * newlines and refilled to width w, after a leading newline.
 *
 * @param s - The input text.
 * @param w - The maximum line width.
 * @returns The formatted text.
 * @see SymPy `sympy.utilities.misc.filldedent`
 */
export function filldedent(s: string, w = 70): string {
  return `\n${fill(dedent(s).replace(/^\n+|\n+$/g, ''), w)}`;
}

/** The characters of a string as Python counts them: code points. */
const codePoints = (s: string): string[] => Array.from(s);

/** Python repr() of a string: in single quotes unless it has one and no double quote, with escapes. */
function pyStrRepr(s: string): string {
  const q = s.includes("'") && !s.includes('"') ? '"' : "'";
  const esc: Readonly<Record<string, string>> = { '\\': '\\\\', '\n': '\\n', '\r': '\\r', '\t': '\\t', [q]: `\\${q}` };
  let out = '';
  for (const ch of s) {
    const code = ch.charCodeAt(0);
    out += esc[ch] ?? (code < 0x20 || code === 0x7f ? `\\x${code.toString(16).padStart(2, '0')}` : ch);
  }
  return `${q}${out}${q}`;
}

/**
 * Source text that, when printed, gives the string `s`
 * of several lines: a call of `dedent` on a triple-quoted string, or a
 * parenthesized concatenation of string literals when a line ends with a
 * space, the text has a backslash, or has both kinds of triple quotes. A
 * single line is its repr.
 *
 * @param s - The input text.
 * @returns The formatted text.
 * @see SymPy `sympy.utilities.misc.rawlines`
 * @example
 * ```ts
 * import { rawlines } from '@symjs/symjs';
 * rawlines('this\nthat'); // => dedent('''\
 * //       this
 * //       that''')
 * ```
 */
export function rawlines(s: string): string {
  const lines = s.split('\n');
  if (lines.length === 1) return pyStrRepr(s);
  const single = s.includes("'''");
  if (lines.some((li) => li.endsWith(' ')) || s.includes('\\') || (single && s.includes('"""'))) {
    const trailing = s.endsWith('\n');
    const lastIndex = lines.length - 1;
    const rv = lines.map((li, i) => pyStrRepr(i !== lastIndex || trailing ? `${li}\n` : li));
    return `(\n    ${rv.join('\n    ')}\n)`;
  }
  const rv = lines.join('\n    ');
  const q = single ? '"""' : "'''";
  return `dedent(${q}\\\n    ${rv}${q})`;
}

/**
 * Source text of a long string as
 * a parenthesized concatenation of literals of at most `c` characters
 * (raw literals when it has a backslash); with `short`, a string that fits
 * on one line is a single literal. A string of several lines is
 * {@link rawlines}.
 *
 * @param s - The input text.
 * @param c - The maximum line width.
 * @param short - Whether to retain a short single-line representation.
 * @returns The formatted text.
 * @see SymPy `sympy.utilities.misc.strlines`
 * @example
 * ```ts
 * import { strlines } from '@symjs/symjs';
 * strlines('this is a long string that should be broken into shorter lines', 40); // => (
 * //   'this is a long string that should be b'
 * //   'roken into shorter lines'
 * //   )
 * ```
 */
export function strlines(s: string, c = 64, short = false): string {
  if (s.includes('\n')) return rawlines(s);
  const q = pyStrRepr(s).startsWith('"') ? '"' : "'";
  const raw = s.includes('\\');
  const r = raw ? 'r' : '';
  const width = c - (raw ? 3 : 2);
  if (width < 1) throw new RangeError(`strlines: the width ${c} is too small`);
  const chars = codePoints(s);
  const out: string[] = [];
  for (let i = 0; i < chars.length; i += width) out.push(chars.slice(i, i + width).join(''));
  if (short && out.length === 1) return `${r}${q}${at(out, 0)}${q}`;
  return `(\n${r}${q}${out.join(`${q}\n${r}${q}`)}${q}\n)`;
}

/** The replacements of a map made in one pass, the keys tried in their order at each position (SymPy `_replace`). */
function replaceAll(s: string, reps: ReadonlyMap<string, string>): string {
  if (reps.size === 0) return s;
  const pattern = new RegExp([...reps.keys()].map((k) => k.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('|'), 'g');
  return s.replace(pattern, (m) => getOrThrow(reps, m));
}

/** A replacement given as an `[old, new]` pair. */
const isPair = (r: ReadonlyMap<string, string> | readonly [string, string]): r is readonly [string, string] => Array.isArray(r);

/**
 * Returns ``string`` with all keys in ``reps`` replaced with their corresponding values, longer strings first, irrespective of the order they are given.  ``reps`` may be passed as tuples or a single mapping.
 *
 * @param s - The input text.
 * @param reps - The patterns and replacement strings.
 * @returns The formatted text.
 * @see SymPy `sympy.utilities.misc.replace`
 * @example
 * ```ts
 * import { replaceString } from '@symjs/symjs';
 * replaceString('foo', new Map([['oo', 'ar'], ['f', 'b']])); // => bar
 * ```
 */
export function replaceString(s: string, ...reps: readonly (ReadonlyMap<string, string> | readonly [string, string])[]): string {
  return replaceAll(s, new Map(reps.flatMap((r): (readonly [string, string])[] => (isPair(r) ? [r] : [...r]))));
}

/** A one-character key with a one-character value (a translation rather than a replacement). */
const isCharPair = ([k, v]: readonly [string, string]): boolean => codePoints(k).length === 1 && codePoints(v).length === 1;

/**
 * The characters of `a` replaced
 * by those of `b` and the characters of `c` deleted (deletion first). With
 * `a` null, the characters of `b` are deleted. `a` may be a map: its
 * one-character keys with one-character values are translated, the other
 * keys are replaced as substrings (in the map's order), and `b` is then the
 * characters to delete.
 *
 * @param s - The input text.
 * @param a - The first operand.
 * @param b - The second operand.
 * @param c - The constant coefficient.
 * @returns The characters of `a` replaced by those of `b` and the characters of `c` deleted (deletion first).
 * @throws RangeError when oldchars and newchars have different lengths.
 * @see SymPy `sympy.utilities.misc.translate`
 * @example
 * ```ts
 * import { translate } from '@symjs/symjs';
 * translate('alphahatdotprime'); // => {\dot{\hat{\alpha}}}'
 * ```
 */
export function translate(s: string, a?: string | ReadonlyMap<string, string> | null, b: string | null = null, c: string | null = null): string {
  if (a === undefined) return translateSymbol(s);
  let mr = new Map<string, string>();
  let from = '';
  let to = '';
  let del = c;
  if (a === null) {
    if (c !== null) throw new TypeError(`c should be None when a=None is passed, instead got ${c}`);
    if (b === null) return s;
    del = b;
  } else if (typeof a !== 'string') {
    const pairs = [...a];
    const short = pairs.filter(isCharPair);
    mr = new Map(pairs.filter((p) => !isCharPair(p)));
    del = b;
    from = short.map(([k]) => k).join('');
    to = short.map(([, v]) => v).join('');
  } else {
    from = a;
    to = b ?? '';
    if (codePoints(from).length !== codePoints(to).length) throw new RangeError('oldchars and newchars have different lengths');
  }
  const gone = new Set(codePoints(del ?? ''));
  const kept = codePoints(s).filter((ch) => !gone.has(ch)).join('');
  const toChars = codePoints(to);
  const tr = new Map(codePoints(from).map((ch, i) => [ch, at(toChars, i)]));
  return codePoints(replaceAll(kept, mr)).map((ch) => tr.get(ch) ?? ch).join('');
}

/** The exact integer value of a float, undefined when it has a fractional part (a normalized mantissa is odd). */
function floatInteger(f: Float): bigint | undefined {
  const { man, exp } = f.mpf;
  return exp >= 0n ? man << exp : undefined;
}

/**
 * Converts an integral value to a bigint. Strict mode accepts integer inputs directly. With strict mode disabled, conversion also accepts values that compare equal to their integer representation.
 *
 * @param n - The value to convert.
 * @param strict - Whether the input must already represent an integer.
 * @returns The exact integer as a bigint.
 * @throws TypeError when the value cannot be converted to an integer in the requested mode.
 * @see SymPy `sympy.utilities.misc.as_int`
 * @example
 * ```ts
 * import { asInt } from '@symjs/symjs';
 * asInt(3); // => 3
 * ```
 */
export function asInt(n: unknown, strict = true): bigint {
  if (typeof n === 'bigint') return n;
  if (typeof n === 'number' && Number.isInteger(n)) return BigInt(n);
  if (n instanceof Rational && n.q === 1n) return n.p;
  if (!strict && typeof n === 'boolean') return n ? 1n : 0n;
  const v = !strict && n instanceof Float ? floatInteger(n) : undefined;
  if (v !== undefined) return v;
  throw new TypeError(`${String(n)} is not an integer`);
}

/**
 * The integer with its English ordinal suffix
 * (`ordinal(1)` is `'1st'`, `ordinal(12)` is `'12th'`, `ordinal(-1)` is
 * `'-1st'`).
 *
 * @param num - The integer to format with an ordinal suffix.
 * @returns The integer with its English ordinal suffix.
 * @see SymPy `sympy.utilities.misc.ordinal`
 */
export function ordinal(num: unknown): string {
  const n = asInt(num);
  const k = (n < 0n ? -n : n) % 100n;
  const suffix = k >= 11n && k <= 13n ? 'th' : ({ 1: 'st', 2: 'nd', 3: 'rd' } as Partial<Record<string, string>>)[String(k % 10n)] ?? 'th';
  return `${n}${suffix}`;
}

/** The short names of the relations (`funcName` with `short`). */
const SHORT_NAMES: Readonly<Record<string, string>> = {
  GreaterThan: 'Ge',
  StrictGreaterThan: 'Gt',
  LessThan: 'Le',
  StrictLessThan: 'Lt',
  Equality: 'Eq',
  Unequality: 'Ne',
};

/** The Python type name of a value that is not an expression. */
function typeName(x: unknown): string {
  if (typeof x === 'bigint' || (typeof x === 'number' && Number.isInteger(x))) return 'int';
  if (typeof x === 'number') return 'float';
  if (typeof x === 'string') return 'str';
  if (typeof x === 'boolean') return 'bool';
  if (typeof x === 'function') return x.name || 'function';
  if (x === null || x === undefined) return 'NoneType';
  if (Array.isArray(x)) return 'list';
  if (x instanceof Map) return 'dict';
  if (x instanceof Set) return 'set';
  // a matrix (rows, cols and get) is SymPy's Matrix, a MutableDenseMatrix
  if (typeof x === 'object' && 'rows' in x && 'cols' in x && 'get' in x) return 'MutableDenseMatrix';
  return 'object';
}

/**
 * The name of the class (or function)
 * of `x`: `Add`, `sin`, `StrictLessThan`, `Integer`, `MutableDenseMatrix`,
 * `int`, ...; with `short`, a relation by its short name (`Lt`).
 *
 * @param x - The value to examine.
 * @param short - Whether to omit the qualification from the displayed name.
 * @returns The name of the class (or function) of `x`: `Add`, `sin`, `StrictLessThan`, `Integer`, `MutableDenseMatrix`, `int`,.
 * @see SymPy `sympy.utilities.misc.func_name`
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 * import { funcName } from '@symjs/symjs/utilities';
 * funcName(ex`x < 1`); // => StrictLessThan
 * ```
 */
export function funcName(x: unknown, short = false): string {
  const rv = x instanceof Expr ? nodeClassName(x) : typeName(x);
  return short ? (SHORT_NAMES[rv] ?? rv) : rv;
}
