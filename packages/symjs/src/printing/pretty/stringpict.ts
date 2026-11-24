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

/**
 * An ASCII (or unicode) picture of equal-length lines.
 *
 * @see SymPy `sympy.printing.pretty.stringpict.stringPict`
 */
export class StringPict {
  /**
   * A horizontal rule spanning the width of the surrounding picture.
   *
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.LINE`
   */
  static readonly LINE: typeof LINE = LINE;

  /** The source string. */
  readonly s: string;
  /** The lines of the picture, all of the same width. */
  readonly picture: string[];
  /** The line number of the baseline. */
  baseline: number;

  /**
   * Creates a StringPict instance.
   *
   * @param s - The input text.
   * @param baseline - The row aligned with the baseline of adjacent forms.
   */
  constructor(s: string, baseline = 0) {
    this.s = s;
    this.picture = StringPict.equalLengths(splitLines(s));
    this.baseline = baseline;
  }

  /**
   * Center lines to a common width.
   *
   * @param lines - The lines to pad to a common width.
   * @returns The lines padded to a common width.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.equalLengths`
   */
  static equalLengths(lines: readonly string[]): string[] {
    if (lines.length === 0) return [''];
    const width = Math.max(...lines.map(lineWidth));
    return lines.map((l) => center(l, width));
  }

  /**
   * Returns the height of the picture in characters.
   *
   * @returns The height of the picture in characters.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.height`
   */
  height(): number {
    return this.picture.length;
  }

  /**
   * Returns the width of the picture in characters.
   *
   * @returns The width of the picture in characters.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.width`
   */
  width(): number {
    return lineWidth(firstOf(this.picture));
  }

  /**
   * Put pictures next to each other, aligned on their baselines.
   *
   * @param args - The operands in their defining order.
   * @returns The resulting text picture and its baseline.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.next`
   */
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

  /**
   * Put pictures to the right of this one.
   *
   * @param args - The operands in their defining order.
   * @returns The resulting text picture and its baseline.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.right`
   */
  right(...args: PictLike[]): PictPair {
    return StringPict.next(this, ...args);
  }

  /**
   * Put pictures (left to right) to the left of this one.
   *
   * @param args - The operands in their defining order.
   * @returns The resulting text picture and its baseline.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.left`
   */
  left(...args: PictLike[]): PictPair {
    return StringPict.next(...args, this);
  }

  /**
   * Put pictures on top of each other, centered.
   * The baseline is that of the second picture.
   *
   * @param args - The operands in their defining order.
   * @returns The resulting text picture and its baseline.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.stack`
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

  /**
   * Put pictures under this one; the baseline stays that of this picture.
   *
   * @param args - The operands in their defining order.
   * @returns The resulting text picture and its baseline.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.below`
   */
  below(...args: (PictLike | typeof LINE)[]): PictPair {
    const [s] = StringPict.stack(this, ...args);
    return [s, this.baseline];
  }

  /**
   * Put pictures above this one; the baseline stays that of this picture.
   *
   * @param args - The operands in their defining order.
   * @returns The resulting text picture and its baseline.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.above`
   */
  above(...args: (PictLike | typeof LINE)[]): PictPair {
    const [s] = StringPict.stack(...args, this);
    return [s, splitLines(s).length - this.height() + this.baseline];
  }

  /**
   * Put parentheses (or other brackets: '[', '{', '|', 'lfloor', ...) around
   * this picture; an empty or undefined side has none.
   *
   * @param left - The left delimiter.
   * @param right - The right delimiter.
   * @param ifasciiNougly - Whether to omit oversized delimiters in ASCII mode.
   * @returns The resulting text picture and its baseline.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.parens`
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

  /**
   * Precede the picture by a slash of the proper size.
   *
   * @returns The resulting text picture and its baseline.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.leftslash`
   */
  leftslash(): PictPair {
    const height = Math.max(this.baseline, this.height() - 1 - this.baseline) * 2 + 1;
    const lines: string[] = [];
    for (let i = 0; i < height; i++) lines.push(' '.repeat(height - i - 1) + hobj('/', 1) + ' '.repeat(i));
    return this.left(new StringPict(lines.join('\n'), Math.floor(height / 2)));
  }

  /**
   * The picture as a string, broken into chunks
   * of `numColumns` (default 80) columns when `wrapLine` is not false.
   *
   * @param options - The render settings.
   * @returns The formatted text.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.render`
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

  /**
   * Does the picture equal the string (lines joined by newlines) or another picture?
   *
   * @param o - The picture to compare.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.printing.pretty.stringpict.stringPict.__eq__`
   */
  equals(o: unknown): boolean {
    if (typeof o === 'string') return this.picture.join('\n') === o;
    if (o instanceof StringPict) return o.picture.length === this.picture.length && o.picture.every((l, i) => l === this.picture[i]);
    return false;
  }

  /**
   * Formats this value as a string.
   *
   * @returns The formatted text.
   */
  toString(): string {
    return this.picture.join('\n');
  }
}

/** SymPy `prettyForm` binding powers. */
export const Binding = { ATOM: 0, FUNC: 1, DIV: 2, POW: 3, MUL: 4, ADD: 5, NEG: 6, OPEN: 7, LINE: 8 } as const;

/**
 * A {@link StringPict} with a binding power used to
 * decide where parentheses are needed when combined.
 *
 * @see SymPy `sympy.printing.pretty.stringpict.prettyForm`
 */
export class PrettyForm extends StringPict {
  /**
   * The binding level for atoms.
   *
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.ATOM`
   */
  static readonly ATOM = Binding.ATOM;
  /**
   * The binding level for function applications.
   *
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.FUNC`
   */
  static readonly FUNC = Binding.FUNC;
  /**
   * The binding level for fractions.
   *
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.DIV`
   */
  static readonly DIV = Binding.DIV;
  /**
   * The binding level for powers.
   *
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.POW`
   */
  static readonly POW = Binding.POW;
  /**
   * The binding level for products.
   *
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.MUL`
   */
  static readonly MUL = Binding.MUL;
  /**
   * The binding level for sums.
   *
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.ADD`
   */
  static readonly ADD = Binding.ADD;
  /**
   * The binding level for negation.
   *
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.NEG`
   */
  static readonly NEG = Binding.NEG;
  /**
   * The binding level for ungrouped forms.
   *
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.OPEN`
   */
  static readonly OPEN = Binding.OPEN;

  /** The binding strength used to decide when parentheses are needed. */
  binding: number;
  /** For function applications: the function name part (used by powers like sin²(x)). */
  prettyFunc: StringPict | undefined;
  /** For function applications: the parenthesized arguments. */
  prettyArgs: StringPict | undefined;

  /**
   * Creates a PrettyForm instance.
   *
   * @param s - The input text.
   * @param baseline - The row aligned with the baseline of adjacent forms.
   * @param binding - The operator binding strength used when adding parentheses.
   */
  constructor(s: string, baseline = 0, binding: number = Binding.ATOM) {
    super(s, baseline);
    this.binding = binding;
  }

  /**
   * Returns a prettyForm from a `(string, baseline)` pair.
   *
   * @param pair - The picture text and its baseline.
   * @param binding - The operator binding strength used when adding parentheses.
   * @returns A prettyForm from a `(string, baseline)` pair.
   */
  static of(pair: PictPair, binding: number = Binding.ATOM): PrettyForm {
    return new PrettyForm(pair[0], pair[1], binding);
  }

  /**
   * A sum; negative terms reuse their minus sign.
   *
   * @param forms - The typeset summands.
   * @returns A sum.
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.__add__`
   */
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

  /**
   * Returns a stacked fraction.
   *
   * @param den - The denominator polynomial.
   * @returns A stacked fraction.
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.__truediv__`
   */
  div(den: PrettyForm): PrettyForm {
    let num: StringPict = this;
    let d: StringPict = den;
    if (this.binding === Binding.DIV) num = new StringPict(...this.parens());
    if (den.binding === Binding.DIV) d = new StringPict(...den.parens());
    if (this.binding === Binding.NEG) num = new StringPict(num.right(' ')[0]);
    return PrettyForm.of(StringPict.stack(num, LINE, d), Binding.DIV);
  }

  /**
   * A product; `-1*x` prints as `-x`.
   *
   * @param first - The first typeset factor.
   * @param others - The remaining factors in display order.
   * @returns A product.
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.__mul__`
   */
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

  /**
   * A power with the exponent raised; `sin(x)**2` prints as sin²(x).
   *
   * @param b0 - The typeset exponent.
   * @returns A power with the exponent raised.
   * @see SymPy `sympy.printing.pretty.stringpict.prettyForm.__pow__`
   */
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
