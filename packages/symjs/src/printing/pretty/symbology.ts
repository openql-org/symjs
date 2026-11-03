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

/** The unicode flag (SymPy `_use_unicode`). Mutated only through {@link prettyUseUnicode}. */
const state: { useUnicode: boolean; mulSymbol: string | undefined } = { useUnicode: false, mulSymbol: undefined };

/**
 * SymPy `pretty_use_unicode(flag=None)`: with no argument return whether
 * unicode is used; otherwise set it and return the previous value.
 */
export function prettyUseUnicode(flag?: boolean): boolean {
  const prev = state.useUnicode;
  if (flag !== undefined) state.useUnicode = flag;
  return prev;
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

/** SymPy `greek_unicode`: greek letter name -> character (`alpha` -> α, `Gamma` -> Γ). */
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

/** SymPy `sub`: symbol -> unicode subscript. */
export const sub: ReadonlyMap<string, string> = /* @__PURE__ */ new Map([
  ['a', 'ₐ'], ['e', 'ₑ'], ['i', 'ᵢ'], ['o', 'ₒ'], ['r', 'ᵣ'], ['u', 'ᵤ'], ['v', 'ᵥ'],
  ['x', 'ₓ'], ['h', 'ₕ'], ['k', 'ₖ'], ['l', 'ₗ'], ['m', 'ₘ'], ['n', 'ₙ'], ['p', 'ₚ'],
  ['s', 'ₛ'], ['t', 'ₜ'], ['beta', 'ᵦ'], ['gamma', 'ᵧ'], ['rho', 'ᵨ'], ['phi', 'ᵩ'],
  ['chi', 'ᵪ'], ['0', '₀'], ['1', '₁'], ['2', '₂'], ['3', '₃'], ['4', '₄'], ['5', '₅'],
  ['6', '₆'], ['7', '₇'], ['8', '₈'], ['9', '₉'], ['+', '₊'], ['-', '₋'], ['=', '₌'],
  ['(', '₍'], [')', '₎'],
]);

/** SymPy `sup`: symbol -> unicode superscript. */
export const sup: ReadonlyMap<string, string> = /* @__PURE__ */ new Map([
  ['i', 'ⁱ'], ['n', 'ⁿ'], ['0', '⁰'], ['1', '¹'], ['2', '²'], ['3', '³'], ['4', '⁴'],
  ['5', '⁵'], ['6', '⁶'], ['7', '⁷'], ['8', '⁸'], ['9', '⁹'], ['+', '⁺'], ['-', '⁻'],
  ['=', '⁼'], ['(', '⁽'], [')', '⁾'],
]);

/** SymPy `center_accent`: insert a combining accent after the middle character. */
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
 * SymPy `xobj(symb, length)`: a spatial object (bracket, integral sign, ...)
 * of the given length, as one string (length 1) or a list of lines.
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

/** SymPy `vobj`: vertical object of the given height (lines joined by newlines). */
export function vobj(symb: string, height: number): string {
  return asLines(xobj(symb, height)).join('\n');
}

/** SymPy `hobj`: horizontal object of the given width. */
export function hobj(symb: string, width: number): string {
  return asLines(xobj(symb, width)).join('');
}

/** SymPy `root`: single-character radicals. */
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

/** SymPy `xsym`: symbology for an operator character. */
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
 * SymPy `pretty_atom(atom_name, default)`: the unicode form of an atom, or
 * `fallback` in ASCII mode. Undefined when there is no form (SymPy raises
 * KeyError and the printer falls back to the str form).
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

/** SymPy `split_super_sub`: name, superscripts and subscripts of a symbol name. */
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
  let base = text.slice(0, pos);
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
  const m = /^([\p{L}\p{M}\p{Nl}\p{No}]+)(\p{Nd}+)$/u.exec(base);
  if (m) {
    base = defined(m[1]);
    subs.unshift(defined(m[2]));
  }
  return [base, supers, subs];
}

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

/** SymPy `pretty_symbol`: the printed form of a symbol name (`alpha_1` -> α₁ in unicode). */
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

/** SymPy `is_subscriptable_in_unicode`. */
export function isSubscriptableInUnicode(subscript: string): boolean {
  return Array.from(subscript).every((c) => sub.has(c));
}

// ---------------------------------------------------------------------------
// Widths and centering
// ---------------------------------------------------------------------------

/** SymPy `is_combining`: is the character a combining modifier (zero width)? */
export function isCombining(ch: string): boolean {
  const c = ch.codePointAt(0) ?? 0;
  return (c >= 0x300 && c < 0x36f) || (c >= 0x20d0 && c < 0x20f0);
}

/** SymPy `line_width`: number of code points, combining characters excluded. */
export function lineWidth(line: string): number {
  let n = 0;
  for (const ch of line) if (!isCombining(ch)) n++;
  return n;
}

/** SymPy `center_pad`: left and right padding to center a width in a target width. */
export function centerPad(wstring: number, wtarget: number, fillchar = ' '): [string, string] {
  if (wstring > wtarget) throw new RangeError('not enough space for string');
  const wdelta = wtarget - wstring;
  const wleft = Math.floor(wdelta / 2);
  return [fillchar.repeat(wleft), fillchar.repeat(wdelta - wleft)];
}

/** SymPy `center`: the string centered in the given width. */
export function center(s: string, width: number, fillchar = ' '): string {
  const [l, r] = centerPad(lineWidth(s), width, fillchar);
  return l + s + r;
}
