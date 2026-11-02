// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of SymPy's `sympy.printing.pretty.stringpict`: `stringPict`, a
 * 2D picture made of equal-width lines with a baseline, and `prettyForm`,
 * which adds a binding power and the arithmetic layout rules (sums,
 * products, fractions and powers).
 *
 * The methods that SymPy returns as `(string, baseline)` tuples return a
 * {@link PictPair} here; `new StringPict(...pair)` / `PrettyForm.of(pair)`
 * rebuild a picture from it.
 */

import { at, defined, first as firstOf } from '../../core/guard';
import { center, hobj, lineWidth, prettyUseUnicode, vobj, xsym } from './symbology';

/** A picture as a string and its baseline (SymPy's `(s, baseline)` tuples). */
export type PictPair = [string, number];

/** Argument of the layout functions: a picture or a (multi-line) string. */
export type PictLike = StringPict | string;

/** Marker for {@link StringPict.stack}: a horizontal line as wide as the widest picture. */
export const LINE: unique symbol = Symbol('stringPict.LINE');

const toPict = (x: PictLike): StringPict => (typeof x === 'string' ? new StringPict(x) : x);

/** Python's str.splitlines for the separators the printers produce. */
function splitLines(s: string): string[] {
  // oxlint-disable-next-line no-control-regex -- Python's splitlines separators include control characters
  const lines = s.split(/\r\n|[\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029]/u);
  if (lines.length > 0 && lines[lines.length - 1] === '') lines.pop();
  return lines;
}

/** Options of {@link StringPict.render} (SymPy `render(**settings)`). */
export interface RenderOptions {
  /** Break lines longer than `numColumns` (default true). */
  readonly wrapLine?: boolean;
  /** Width at which lines are broken (default 80). */
  readonly numColumns?: number;
  /** Use the unicode overflow arrows. */
  readonly useUnicode?: boolean;
}

/** SymPy `stringPict`: an ASCII (or unicode) picture of equal-length lines. */
export class StringPict {
  /** SymPy `stringPict.LINE`. */
  static readonly LINE: typeof LINE = LINE;

  /** The source string. */
  readonly s: string;
  /** The lines of the picture, all of the same width. */
  readonly picture: string[];
  /** The line number of the baseline. */
  baseline: number;

  constructor(s: string, baseline = 0) {
    this.s = s;
    this.picture = StringPict.equalLengths(splitLines(s));
    this.baseline = baseline;
  }

  /** SymPy `equalLengths`: center lines to a common width. */
  static equalLengths(lines: readonly string[]): string[] {
    if (lines.length === 0) return [''];
    const width = Math.max(...lines.map(lineWidth));
    return lines.map((l) => center(l, width));
  }

  /** The height of the picture in characters. */
  height(): number {
    return this.picture.length;
  }

  /** The width of the picture in characters. */
  width(): number {
    return lineWidth(firstOf(this.picture));
  }

  /** SymPy `stringPict.next`: put pictures next to each other, aligned on their baselines. */
  static next(...args: PictLike[]): PictPair {
    const objects = args.map(toPict);
    const newBaseline = Math.max(...objects.map((o) => o.baseline));
    const newHeightBelow = Math.max(...objects.map((o) => o.height() - o.baseline));
    const newHeight = newBaseline + newHeightBelow;
    const pictures = objects.map((o) => {
      const empty = ' '.repeat(o.width());
      const basePadding = newBaseline - o.baseline;
      const totalPadding = newHeight - o.height();
      return [
        ...Array<string>(basePadding).fill(empty),
        ...o.picture,
        ...Array<string>(totalPadding - basePadding).fill(empty),
      ];
    });
    const n = Math.min(...pictures.map((p) => p.length));
    const result: string[] = [];
    for (let i = 0; i < n; i++) result.push(pictures.map((p) => at(p, i)).join(''));
    return [result.join('\n'), newBaseline];
  }

  /** Put pictures to the right of this one. */
  right(...args: PictLike[]): PictPair {
    return StringPict.next(this, ...args);
  }

  /** Put pictures (left to right) to the left of this one. */
  left(...args: PictLike[]): PictPair {
    return StringPict.next(...args, this);
  }

  /**
   * SymPy `stringPict.stack`: put pictures on top of each other, centered.
   * The baseline is that of the second picture.
   */
  static stack(...args: (PictLike | typeof LINE)[]): PictPair {
    const objects0 = args.map((a) => (a === LINE ? a : toPict(a)));
    const newWidth = Math.max(...objects0.filter((o): o is StringPict => o !== LINE).map((o) => o.width()));
    const lineObj = new StringPict(hobj('-', newWidth));
    const objects = objects0.map((o) => (o === LINE ? lineObj : o));
    const newPicture = objects.flatMap((o) => o.picture.map((l) => center(l, newWidth)));
    const newBaseline = at(objects, 0).height() + at(objects, 1).baseline;
    return [newPicture.join('\n'), newBaseline];
  }

  /** Put pictures under this one; the baseline stays that of this picture. */
  below(...args: (PictLike | typeof LINE)[]): PictPair {
    const [s] = StringPict.stack(this, ...args);
    return [s, this.baseline];
  }

  /** Put pictures above this one; the baseline stays that of this picture. */
  above(...args: (PictLike | typeof LINE)[]): PictPair {
    const [s] = StringPict.stack(...args, this);
    return [s, splitLines(s).length - this.height() + this.baseline];
  }

  /**
   * Put parentheses (or other brackets: '[', '{', '|', 'lfloor', ...) around
   * this picture; an empty or undefined side has none.
   */
  parens(left: string | undefined = '(', right: string | undefined = ')', ifasciiNougly = false): PictPair {
    let h = this.height();
    let b = this.baseline;
    if (ifasciiNougly && !prettyUseUnicode()) {
      h = 1;
      b = 0;
    }
    let res: StringPict = this;
    if (left) {
      const lparen = new StringPict(vobj(left, h), b);
      res = new StringPict(...lparen.right(this));
    }
    if (right) {
      const rparen = new StringPict(vobj(right, h), b);
      res = new StringPict(...res.right(rparen));
    }
    return [res.picture.join('\n'), res.baseline];
  }

  /** Precede the picture by a slash of the proper size. */
  leftslash(): PictPair {
    const height = Math.max(this.baseline, this.height() - 1 - this.baseline) * 2 + 1;
    const lines: string[] = [];
    for (let i = 0; i < height; i++) lines.push(' '.repeat(height - i - 1) + hobj('/', 1) + ' '.repeat(i));
    return this.left(new StringPict(lines.join('\n'), Math.floor(height / 2)));
  }

  /**
   * SymPy `stringPict.render`: the picture as a string, broken into chunks
   * of `numColumns` (default 80) columns when `wrapLine` is not false.
   */
  render(options: RenderOptions = {}): string {
    if (options.wrapLine === false) return this.picture.join('\n');
    let ncols = options.numColumns ?? 80;
    if (ncols <= 0) ncols = 80;
    if (this.width() <= ncols) return this.picture.join('\n');

    const unicode = options.useUnicode === true || prettyUseUnicode();
    const overflowStart = unicode ? '↪ ' : '> ';
    const overflowEnd = unicode ? ' ↪' : ' >';
    const chunks = (line: string): string[] => {
      const chars = Array.from(line);
      const out: string[] = [];
      let prefix = '';
      let width = lineWidth(prefix + overflowEnd);
      let start = 0;
      chars.forEach((x, i) => {
        const wx = lineWidth(x);
        if (width + wx > ncols) {
          out.push(prefix + chars.slice(start, i).join('') + overflowEnd);
          prefix = overflowStart;
          width = lineWidth(prefix + overflowEnd);
          start = i;
        }
        width += wx;
      });
      out.push(prefix + chars.slice(start).join(''));
      return out;
    };
    const all = this.picture.map(chunks);
    const n = Math.min(...all.map((c) => c.length));
    const screens: string[] = [];
    for (let i = 0; i < n; i++) screens.push(all.map((c) => at(c, i)).join('\n'));
    return screens.join('\n\n');
  }

  /** Does the picture equal the string (lines joined by newlines) or another picture? */
  equals(o: unknown): boolean {
    if (typeof o === 'string') return this.picture.join('\n') === o;
    if (o instanceof StringPict) return o.picture.length === this.picture.length && o.picture.every((l, i) => l === this.picture[i]);
    return false;
  }

  toString(): string {
    return this.picture.join('\n');
  }
}

/** SymPy `prettyForm` binding powers. */
export const Binding = { ATOM: 0, FUNC: 1, DIV: 2, POW: 3, MUL: 4, ADD: 5, NEG: 6, OPEN: 7, LINE: 8 } as const;

/**
 * SymPy `prettyForm`: a {@link StringPict} with a binding power used to
 * decide where parentheses are needed when combined.
 */
export class PrettyForm extends StringPict {
  static readonly ATOM = Binding.ATOM;
  static readonly FUNC = Binding.FUNC;
  static readonly DIV = Binding.DIV;
  static readonly POW = Binding.POW;
  static readonly MUL = Binding.MUL;
  static readonly ADD = Binding.ADD;
  static readonly NEG = Binding.NEG;
  static readonly OPEN = Binding.OPEN;

  binding: number;
  /** For function applications: the function name part (used by powers like sin²(x)). */
  prettyFunc: StringPict | undefined;
  /** For function applications: the parenthesized arguments. */
  prettyArgs: StringPict | undefined;

  constructor(s: string, baseline = 0, binding: number = Binding.ATOM) {
    super(s, baseline);
    this.binding = binding;
  }

  /** A prettyForm from a `(string, baseline)` pair. */
  static of(pair: PictPair, binding: number = Binding.ATOM): PrettyForm {
    return new PrettyForm(pair[0], pair[1], binding);
  }

  /** SymPy `prettyForm.__add__`: a sum; negative terms reuse their minus sign. */
  static add(...forms: PrettyForm[]): PrettyForm {
    const result: PictLike[] = [];
    forms.forEach((f, i) => {
      let arg: StringPict = f;
      if (f.binding > Binding.NEG) arg = new StringPict(...f.parens());
      if (i > 0 && f.binding !== Binding.NEG) result.push(' + ');
      result.push(arg);
    });
    return PrettyForm.of(StringPict.next(...result), Binding.ADD);
  }

  /** SymPy `prettyForm.__truediv__`: a stacked fraction. */
  div(den: PrettyForm): PrettyForm {
    let num: StringPict = this;
    let d: StringPict = den;
    if (this.binding === Binding.DIV) num = new StringPict(...this.parens());
    if (den.binding === Binding.DIV) d = new StringPict(...den.parens());
    if (this.binding === Binding.NEG) num = new StringPict(num.right(' ')[0]);
    return PrettyForm.of(StringPict.stack(num, LINE, d), Binding.DIV);
  }

  /** SymPy `prettyForm.__mul__`: a product; `-1*x` prints as `-x`. */
  static mul(first: PrettyForm, ...others: PrettyForm[]): PrettyForm {
    if (others.length === 0) return first;
    const degree = '°';
    const result: PictLike[] = [];
    let arg: StringPict = first;
    if (first.binding > Binding.MUL && first.binding !== Binding.NEG) arg = new StringPict(...first.parens());
    result.push(arg);
    for (const o of others) {
      if (o.picture[0] !== degree) result.push(xsym('*'));
      let a: StringPict = o;
      if (o.binding > Binding.MUL && o.binding !== Binding.NEG) a = new StringPict(...o.parens());
      result.push(a);
    }
    const eq = (x: PictLike | undefined, s: string): boolean => (typeof x === 'string' ? x === s : x?.equals(s) === true);
    const len = result.length;
    for (let i = 0; i < len; i++) {
      if (i < len - 1 && eq(result[i], '-1') && eq(result[i + 1], xsym('*'))) result.splice(i, 2, '-');
    }
    const head = firstOf(result);
    const firstChar = typeof head === 'string' ? head[0] : firstOf(head.picture)[0];
    let bin: number;
    if (firstChar === '-') {
      bin = Binding.NEG;
      if (eq(head, '-')) {
        const right = at(result, 1);
        const rp = toPict(right);
        if (defined(rp.picture[rp.baseline])[0] === '-') result[0] = '- ';
      }
    } else {
      bin = Binding.MUL;
    }
    return PrettyForm.of(StringPict.next(...result), bin);
  }

  /** SymPy `prettyForm.__pow__`: a power with the exponent raised; `sin(x)**2` prints as sin²(x). */
  pow(b0: PrettyForm): PrettyForm {
    let a: StringPict = this;
    let b: StringPict = b0;
    let inlineFunc = false;
    if (b0.binding === Binding.POW) b = new StringPict(...b0.parens());
    if (this.binding > Binding.FUNC) a = new StringPict(...this.parens());
    else if (this.binding === Binding.FUNC) {
      if (b.height() > 1) a = new StringPict(...this.parens());
      else inlineFunc = true;
    }
    if (inlineFunc && this.prettyFunc !== undefined && this.prettyArgs !== undefined) {
      b.baseline = this.prettyFunc.baseline + b.height();
      const func = new StringPict(...this.prettyFunc.right(b));
      return PrettyForm.of(func.right(this.prettyArgs));
    }
    const top = new StringPict(...b.left(' '.repeat(a.width())));
    const bot = new StringPict(...a.right(' '.repeat(b.width())));
    return PrettyForm.of(bot.above(top), Binding.POW);
  }
}
