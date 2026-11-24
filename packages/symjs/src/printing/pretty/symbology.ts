// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of SymPy's `sympy.printing.pretty.pretty_symbology`: the
 * unicode/ASCII symbol tables (greek letters, sub- and superscripts,
 * brackets, radicals, atoms) and the helpers that build vertical and
 * horizontal objects of a given size.
 *
 * Like SymPy, the choice between unicode and ASCII is a module-wide flag
 * ({@link prettyUseUnicode}) that the pretty printer sets for the duration
 * of a call and restores afterwards.
 */

import { at, defined } from '../../core/guard';
import { splitSuperSub } from '../conventions';

/**
 * The unicode flag (SymPy `_use_unicode`). Mutated only through {@link prettyUseUnicode}.
 * JavaScript strings are unicode, so it starts true (SymPy starts without unicode until a
 * terminal that supports it is detected).
 */
const state: { useUnicode: boolean; mulSymbol: string | undefined } = { useUnicode: true, mulSymbol: undefined };

/**
 * Returns the current Unicode printing setting. Supplying `flag` changes the setting and
 * returns its previous value.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.pretty_use_unicode`
 */
export function prettyUseUnicode(flag?: boolean): boolean {
  const prev = state.useUnicode;
  if (flag !== undefined) state.useUnicode = flag;
  return prev;
}

/**
 * Enables Unicode output for the pretty printer.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.pretty_try_use_unicode`
 */
export function prettyTryUseUnicode(): void {
  state.useUnicode = true;
}

// ---------------------------------------------------------------------------
// Greek letters
// ---------------------------------------------------------------------------

const GREEK_NAMES = [
  'alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lamda', 'mu', 'nu', 'xi',
  'omicron', 'pi', 'rho', 'sigma', 'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega',
] as const;

function buildGreek(): ReadonlyMap<string, string> {
  const m = new Map<string, string>();
  GREEK_NAMES.forEach((name, i) => {
    // U+03B1.. small letters, U+0391.. capitals; final sigma (U+03C2) and the
    // gap at U+03A2 are skipped by the alphabet order after rho.
    const offset = i >= 17 ? i + 1 : i;
    m.set(name, String.fromCodePoint(0x3b1 + offset));
    m.set(at(name, 0).toUpperCase() + name.slice(1), String.fromCodePoint(0x391 + offset));
  });
  m.set('lambda', defined(m.get('lamda')));
  m.set('Lambda', defined(m.get('Lamda')));
  m.set('varsigma', 'ς');
  return m;
}

/**
 * Maps Greek letter names to Unicode characters, such as `alpha` to α and `Gamma` to Γ.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.greek_unicode`
 */
export const greekUnicode: ReadonlyMap<string, string> = /* @__PURE__ */ buildGreek();

const BOLD_GREEK_EXTRA: Readonly<Record<string, string>> = { varsigma: '\u{1d6d3}' };

/** Bold latin letters (SymPy `bold_unicode`). */
function boldLetter(c: string): string | undefined {
  // the first UTF-16 unit of a character outside the BMP is a surrogate, in neither range
  const code = c.charCodeAt(0);
  if (code >= 0x61 && code <= 0x7a) return String.fromCodePoint(0x1d41a + code - 0x61);
  if (code >= 0x41 && code <= 0x5a) return String.fromCodePoint(0x1d400 + code - 0x41);
  return undefined;
}

// ---------------------------------------------------------------------------
// Sub- and superscripts
// ---------------------------------------------------------------------------

/**
 * Maps symbols to their Unicode subscripts.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.sub`
 */
export const sub: ReadonlyMap<string, string> = /* @__PURE__ */ new Map([
  ['a', 'ₐ'], ['e', 'ₑ'], ['i', 'ᵢ'], ['o', 'ₒ'], ['r', 'ᵣ'], ['u', 'ᵤ'], ['v', 'ᵥ'],
  ['x', 'ₓ'], ['h', 'ₕ'], ['k', 'ₖ'], ['l', 'ₗ'], ['m', 'ₘ'], ['n', 'ₙ'], ['p', 'ₚ'],
  ['s', 'ₛ'], ['t', 'ₜ'], ['beta', 'ᵦ'], ['gamma', 'ᵧ'], ['rho', 'ᵨ'], ['phi', 'ᵩ'],
  ['chi', 'ᵪ'], ['0', '₀'], ['1', '₁'], ['2', '₂'], ['3', '₃'], ['4', '₄'], ['5', '₅'],
  ['6', '₆'], ['7', '₇'], ['8', '₈'], ['9', '₉'], ['+', '₊'], ['-', '₋'], ['=', '₌'],
  ['(', '₍'], [')', '₎'],
]);

/**
 * Maps symbols to their Unicode superscripts.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.sup`
 */
export const sup: ReadonlyMap<string, string> = /* @__PURE__ */ new Map([
  ['i', 'ⁱ'], ['n', 'ⁿ'], ['0', '⁰'], ['1', '¹'], ['2', '²'], ['3', '³'], ['4', '⁴'],
  ['5', '⁵'], ['6', '⁶'], ['7', '⁷'], ['8', '⁸'], ['9', '⁹'], ['+', '⁺'], ['-', '⁻'],
  ['=', '⁼'], ['(', '⁽'], [')', '⁾'],
]);

/**
 * Insert a combining accent after the middle character.
 *
 * @param s - The input text.
 * @param accent - The combining accent to insert.
 * @returns The formatted text.
 * @see SymPy `sympy.printing.pretty.pretty_symbology.center_accent`
 */
export function centerAccent(s: string, accent: string): string {
  const cs = Array.from(s);
  const mid = Math.floor(cs.length / 2) + 1;
  return cs.slice(0, mid).join('') + accent + cs.slice(mid).join('');
}

const MODIFIERS: readonly (readonly [string, (s: string) => string])[] = /* @__PURE__ */ (
  [
    ['mathring', (s: string) => centerAccent(s, '̊')],
    ['ddddot', (s: string) => centerAccent(s, '⃜')],
    ['dddot', (s: string) => centerAccent(s, '⃛')],
    ['ddot', (s: string) => centerAccent(s, '̈')],
    ['dot', (s: string) => centerAccent(s, '̇')],
    ['check', (s: string) => centerAccent(s, '̌')],
    ['breve', (s: string) => centerAccent(s, '̆')],
    ['acute', (s: string) => centerAccent(s, '́')],
    ['grave', (s: string) => centerAccent(s, '̀')],
    ['tilde', (s: string) => centerAccent(s, '̃')],
    ['hat', (s: string) => centerAccent(s, '̂')],
    ['bar', (s: string) => centerAccent(s, '̅')],
    ['vec', (s: string) => centerAccent(s, '⃗')],
    ['prime', (s: string) => `${s}′`],
    ['prm', (s: string) => `${s}′`],
    ['norm', (s: string) => `‖${s}‖`],
    ['avg', (s: string) => `⟨${s}⟩`],
    ['abs', (s: string) => `|${s}|`],
    ['mag', (s: string) => `|${s}|`],
  ] as const
)
  .map((x, i) => [x, i] as const)
  // Python's sorted() by decreasing length is stable
  .sort((a, b) => b[0][0].length - a[0][0].length || a[1] - b[1])
  .map(([x]) => x);

// ---------------------------------------------------------------------------
// Vertical and horizontal objects
// ---------------------------------------------------------------------------

/** (extension, top, bottom, middle?) pieces and the one-character form. */
type XObj = string | readonly [readonly string[], string] | readonly string[];

const XOBJ_UNICODE: Readonly<Record<string, XObj>> = {
  '(': [['⎜', '⎛', '⎝'], '('],
  ')': [['⎟', '⎞', '⎠'], ')'],
  '[': [['⎢', '⎡', '⎣'], '['],
  ']': [['⎥', '⎤', '⎦'], ']'],
  '{': [['⎪', '⎧', '⎩', '⎨'], '{'],
  '}': [['⎪', '⎫', '⎭', '⎬'], '}'],
  '|': '│',
  Tee: '┴',
  UpTack: '┬',
  '<': [['│', '╱', '╲'], '<'],
  '>': [['│', '╲', '╱'], '>'],
  lfloor: [['⎢', '⎢', '⎣'], '⌊'],
  rfloor: [['⎥', '⎥', '⎦'], '⌋'],
  lceil: [['⎢', '⎡', '⎢'], '⌈'],
  rceil: [['⎥', '⎤', '⎥'], '⌉'],
  int: [['⎮', '⌠', '⌡'], '∫'],
  sum: [['╲', '_', '‾', '╱'], '∑'],
  '-': '─',
  _: '_',
  '/': '╱',
  '\\': '╲',
};

const XOBJ_ASCII: Readonly<Record<string, XObj>> = {
  '(': [['|', '/', '\\'], '('],
  ')': [['|', '\\', '/'], ')'],
  '[': [['[', '[', '['], '['],
  ']': [[']', ']', ']'], ']'],
  '{': [['|', '/', '\\', '<'], '{'],
  '}': [['|', '\\', '/', '>'], '}'],
  '|': '|',
  '<': [['|', '/', '\\'], '<'],
  '>': [['|', '\\', '/'], '>'],
  int: [' | ', '  /', '/  '],
  '-': '-',
  _: '_',
  '/': '/',
  '\\': '\\',
};

/**
 * Builds an extensible symbol, such as a bracket or integral sign. A symbol of length one is a
 * string. Longer symbols are arrays of parts, with the requested length rounded up to an odd
 * number if a middle piece is required.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.xobj`
 */
export function xobj(symb: string, length: number): string | string[] {
  if (length <= 0) throw new RangeError('Length should be greater than 0');
  const table = state.useUnicode ? XOBJ_UNICODE : XOBJ_ASCII;
  const vinfo = table[symb];
  if (vinfo === undefined) throw new RangeError(`unknown pretty object ${JSON.stringify(symb)}`);
  let c1: string | undefined;
  let ext: string;
  let top: string | undefined;
  let bot: string | undefined;
  let mid: string | undefined;
  if (typeof vinfo === 'string') {
    ext = vinfo;
  } else {
    let vlong: readonly string[];
    const head = vinfo[0];
    const tail = vinfo[1];
    if (typeof head !== 'string' && typeof tail === 'string') {
      vlong = head;
      c1 = tail;
    } else {
      const items: readonly unknown[] = vinfo;
      vlong = items.filter((v): v is string => typeof v === 'string');
    }
    ext = at(vlong, 0);
    top = vlong[1];
    bot = vlong[2];
    mid = vlong[3];
  }
  c1 ??= ext;
  top ??= ext;
  bot ??= ext;
  let len = length;
  if (mid !== undefined) {
    if (len % 2 === 0) len += 1;
  } else {
    mid = ext;
  }
  if (len === 1) return c1;
  const next = Math.floor((len - 2) / 2);
  const nmid = len - 2 - next * 2;
  return [top, ...Array<string>(next).fill(ext), ...Array<string>(nmid).fill(mid), ...Array<string>(next).fill(ext), bot];
}

const asLines = (x: string | string[]): string[] => (typeof x === 'string' ? Array.from(x) : x);

/**
 * Stacks the parts of a vertical symbol for the requested height, joining them with newlines.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.vobj`
 */
export function vobj(symb: string, height: number): string {
  return asLines(xobj(symb, height)).join('\n');
}

/**
 * Joins the parts of a horizontal symbol for the requested width.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.hobj`
 */
export function hobj(symb: string, width: number): string {
  return asLines(xobj(symb, width)).join('');
}

/**
 * Maps the root indices 2, 3 and 4 to their Unicode radical signs.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.root`
 */
export const nthRoot: ReadonlyMap<number, string> = /* @__PURE__ */ new Map([
  [2, '√'],
  [3, '∛'],
  [4, '∜'],
]);

const XSYM: Readonly<Record<string, readonly [string, string]>> = {
  '==': ['=', '='],
  '<': ['<', '<'],
  '>': ['>', '>'],
  '<=': ['<=', '≤'],
  '>=': ['>=', '≥'],
  '!=': ['!=', '≠'],
  ':=': [':=', ':='],
  '+=': ['+=', '+='],
  '-=': ['-=', '-='],
  '*=': ['*=', '*='],
  '/=': ['/=', '/='],
  '%=': ['%=', '%='],
  '*': ['*', '⋅'],
  '-->': ['-->', '——▶'],
  '==>': ['==>', '══▶'],
  '.': ['*', '∘'],
};

/**
 * Set the multiplication symbol used by `xsym('*')` (undefined restores
 * SymPy's ⋅ / *); returns the previous override.
 */
export function prettyMulSymbol(symbol: string | undefined): string | undefined {
  const prev = state.mulSymbol;
  state.mulSymbol = symbol;
  return prev;
}

/**
 * Returns the operator symbol for the current pretty-printing settings.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.xsym`
 */
export function xsym(sym: string): string {
  if (sym === '*' && state.mulSymbol !== undefined) return state.mulSymbol;
  const op = XSYM[sym];
  if (op === undefined) throw new RangeError(`unknown pretty symbol ${JSON.stringify(sym)}`);
  return state.useUnicode ? op[1] : op[0];
}

const ATOMS: Readonly<Record<string, string>> = {
  Exp1: 'ℯ',
  Pi: 'π',
  Infinity: '∞',
  NegativeInfinity: '-∞',
  ImaginaryUnit: 'ⅈ',
  EmptySet: '∅',
  Naturals: 'ℕ',
  Naturals0: 'ℕ₀',
  Integers: 'ℤ',
  Rationals: 'ℚ',
  Reals: 'ℝ',
  Complexes: 'ℂ',
  Universe: '\u{1d54c}',
  IdentityMatrix: '\u{1d540}',
  ZeroMatrix: '\u{1d7d8}',
  OneMatrix: '\u{1d7d9}',
  Differential: 'ⅆ',
  Union: '∪',
  ElementOf: '∈',
  SmallElementOf: '∊',
  SymmetricDifference: '∆',
  Intersection: '∩',
  Ring: '∘',
  Multiplication: '×',
  TensorProduct: '⨂',
  Dots: '…',
  'Modifier Letter Low Ring': '˳',
  EmptySequence: 'EmptySequence',
  SuperscriptPlus: '⁺',
  SuperscriptMinus: '⁻',
  Dagger: '†',
  Degree: '°',
  And: '∧',
  Or: '∨',
  Not: '¬',
  Nor: '⊽',
  Nand: '⊼',
  Xor: '⊻',
  Equiv: '⇔',
  NotEquiv: '⇎',
  Implies: '⇔',
  NotImplies: '⇎',
  Arrow: '→',
  ArrowFromBar: '↦',
  NotArrow: '↛',
  Tautology: '┴',
  Contradiction: '┬',
};

/**
 * Returns the drawing and annotation offsets for the hypergeometric F or Meijer G symbol as
 * `[size, top, bottom, add, picture]`.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.annotated`
 */
export function annotated(letter: 'F' | 'G'): [number, number, number, number, string] {
  if (state.useUnicode) return letter === 'F' ? [2, 0, 2, 0, '┌─\n├─\n╵'] : [3, 0, 3, 1, '╭─╮\n│╶┐\n╰─╯'];
  return letter === 'F' ? [3, 0, 3, 0, ' _\n|_\n|\n'] : [3, 0, 3, 1, ' __\n/__\n\\_|'];
}

/**
 * Looks up the Unicode representation of an atom by name. In ASCII mode it uses the supplied
 * `fallback`.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.pretty_atom`
 */
export function prettyAtom(name: string, fallback?: string, imaginaryUnit: 'i' | 'j' = 'i'): string | undefined {
  if (state.useUnicode) {
    if (name === 'ImaginaryUnit' && imaginaryUnit === 'j') return 'ⅉ';
    return ATOMS[name];
  }
  return fallback;
}

// ---------------------------------------------------------------------------
// Symbol names
// ---------------------------------------------------------------------------

/**
 * Splits a symbol name into its base name, superscripts and subscripts.
 *
 * @see SymPy `sympy.printing.conventions.split_super_sub`
 */
export { splitSuperSub } from '../conventions';

function translateName(s: string, bold: boolean): string {
  const g = bold ? (greekUnicode.get(s) ?? BOLD_GREEK_EXTRA[s]) : greekUnicode.get(s);
  if (g !== undefined) return bold && s === 'varsigma' ? '\u{1d6d3}' : g;
  for (const [key, f] of MODIFIERS) {
    if (s.toLowerCase().endsWith(key) && s.length > key.length) return f(translateName(s.slice(0, -key.length), bold));
  }
  if (bold) {
    return Array.from(s)
      .map((c) => {
        const b = boldLetter(c);
        if (b === undefined) throw new RangeError(`no bold form of ${JSON.stringify(c)}`);
        return b;
      })
      .join('');
  }
  return s;
}

function prettyList(items: readonly string[], mapping: ReadonlyMap<string, string>): string[] | undefined {
  const result: string[] = [];
  for (const s of items) {
    let pretty = mapping.get(s);
    if (pretty === undefined) {
      const chars = Array.from(s).map((c) => mapping.get(c));
      if (chars.some((c) => c === undefined)) return undefined;
      pretty = chars.join('');
    }
    result.push(pretty);
  }
  return result;
}

/**
 * Formats a symbol name for the current output mode, rendering `alpha_1` as α₁ in Unicode.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.pretty_symbol`
 */
export function prettySymbol(symbName: string, boldName = false): string {
  if (!state.useUnicode) return symbName;
  const [name0, sups, subs] = splitSuperSub(symbName);
  let name = translateName(name0, boldName);
  const prettySups = prettyList(sups, sup);
  const prettySubs = prettySups !== undefined ? prettyList(subs, sub) : undefined;
  if (prettySubs === undefined || prettySups === undefined) {
    if (subs.length > 0) name += `_${subs.map((s) => translateName(s, boldName)).join('_')}`;
    if (sups.length > 0) name += `__${sups.map((s) => translateName(s, boldName)).join('__')}`;
    return name;
  }
  return name + prettySups.join(' ') + prettySubs.join(' ');
}

/**
 * Tests whether every character can be written as a Unicode subscript.
 *
 * @param subscript - The text to render below the baseline.
 * @returns Whether each character has a Unicode subscript.
 * @see SymPy `sympy.printing.pretty.pretty_symbology.is_subscriptable_in_unicode`
 * @example
 * ```ts
 * import { isSubscriptableInUnicode } from '@symjs/symjs';
 * isSubscriptableInUnicode('abc'); // => False
 * ```
 */
export function isSubscriptableInUnicode(subscript: string): boolean {
  return Array.from(subscript).every((c) => sub.has(c));
}

// ---------------------------------------------------------------------------
// Widths and centering
// ---------------------------------------------------------------------------

/**
 * Tests whether a character is a combining mark that the pretty printer treats as zero-width.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.is_combining`
 */
export function isCombining(ch: string): boolean {
  const c = ch.codePointAt(0) ?? 0;
  return (c >= 0x300 && c < 0x36f) || (c >= 0x20d0 && c < 0x20f0);
}

/**
 * Counts the code points in a line, excluding combining marks recognized by the pretty
 * printer.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.line_width`
 */
export function lineWidth(line: string): number {
  let n = 0;
  for (const ch of line) if (!isCombining(ch)) n++;
  return n;
}

/**
 * Returns the left and right padding needed to center text of width `wstring` within `wtarget`
 * columns.
 *
 * @see SymPy `sympy.printing.pretty.pretty_symbology.center_pad`
 */
export function centerPad(wstring: number, wtarget: number, fillchar = ' '): [string, string] {
  if (wstring > wtarget) throw new RangeError('not enough space for string');
  const wdelta = wtarget - wstring;
  const wleft = Math.floor(wdelta / 2);
  return [fillchar.repeat(wleft), fillchar.repeat(wdelta - wleft)];
}

/**
 * Returns the string centered in the given width.
 *
 * @param s - The text to center.
 * @param width - The target line width.
 * @param fillchar - The padding character.
 * @returns The string centered in the given width.
 * @see SymPy `sympy.printing.pretty.pretty_symbology.center`
 */
export function center(s: string, width: number, fillchar = ' '): string {
  const [l, r] = centerPad(lineWidth(s), width, fillchar);
  return l + s + r;
}
