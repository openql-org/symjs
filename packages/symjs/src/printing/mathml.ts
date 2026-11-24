// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/printing/mathml.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy's MathML printers: content MathML (`<apply><plus/>...`,
 * `MathMLContentPrinter`) and presentation MathML (`<mrow><mi>x</mi>...`,
 * `MathMLPresentationPrinter`), with `mathml` and `print_mathml`.
 */

import { Add, BoolAtom, Constant, Derivative, Expr, ExtensionExpr, Float, Fn, Integral, Limit, Mul, Piecewise, Pow, Rational, Rel, Special, Sym, UndefFn, impl, isNum } from '../core/nodes';
import { BoolOp } from '../core/boolalg';
import { isNegative } from '../core/assumptions';
import { Concrete } from '../core/concrete';
import { sympify, splitCoeff } from '../core/ops';
import { at } from '../core/guard';
import { sympyClassName } from '../core/compare';
import { precToDps, toStr } from '../numeric/mpf';
import { asOrderedFactors, asOrderedTerms, compareKeys, sortKey } from './sortkey';
import { PREC, declaredPrecedence, precedence as strPrecedence, startsNegative, str } from './str';
import { DOTS, rangePrintForm, setArgsOrdered, setClass } from './sets';
import { requiresPartial } from './conventions';
import { greekUnicode, splitSuperSub } from './pretty/symbology';

// ---------------------------------------------------------------------------
// A minimal XML tree (SymPy builds an xml.dom.minidom document)
// ---------------------------------------------------------------------------

/** An XML element of the MathML output; text children are written as they are (SymPy's raw text nodes). */
export class MathMLElement {
  /** The XML attributes of this MathML element. */
  readonly attributes: [string, string][] = [];
  /** The child nodes in document order. */
  readonly children: (MathMLElement | string)[] = [];
  /**
   * Creates a MathMLElement instance.
   *
   * @param tag - The XML element name.
   */
  constructor(
    /** The MathML element name. */
    readonly tag: string) {}
  /**
   * Appends a child element or text and returns this element.
   *
   * @param children - The child nodes to append in order.
   * @returns This instance.
   */
  append(...children: (MathMLElement | string)[]): this {
    this.children.push(...children);
    return this;
  }
  /**
   * Sets an attribute and returns this element.
   *
   * @param name - The XML attribute name.
   * @param value - The attribute value.
   * @returns This instance.
   */
  set(name: string, value: string): this {
    this.attributes.push([name, value]);
    return this;
  }
  private open(): string {
    return `<${this.tag}${this.attributes.map(([k, v]) => ` ${k}="${v}"`).join('')}`;
  }
  /**
   * Minidom `toxml()`: the element on one line.
   *
   * @returns The formatted text.
   */
  toxml(): string {
    if (this.children.length === 0) return `${this.open()}/>`;
    return `${this.open()}>${this.children.map((c) => (typeof c === 'string' ? c : c.toxml())).join('')}</${this.tag}>`;
  }
  /**
   * Minidom `toprettyxml()`: one element per line, indented with tabs.
   *
   * @param indent - The indentation added for each nested element.
   * @returns The formatted text.
   */
  toprettyxml(indent = ''): string {
    if (this.children.length === 0) return `${indent}${this.open()}/>\n`;
    const only = this.children[0];
    if (this.children.length === 1 && typeof only === 'string') return `${indent}${this.open()}>${only}</${this.tag}>\n`;
    const inner = this.children.map((c) => (typeof c === 'string' ? (c ? `${indent}\t${c}\n` : '') : c.toprettyxml(`${indent}\t`))).join('');
    return `${indent}${this.open()}>\n${inner}${indent}</${this.tag}>\n`;
  }
}

const el = (tag: string, ...children: (MathMLElement | string)[]): MathMLElement => new MathMLElement(tag).append(...children);

/** Python's `encode('ascii', 'xmlcharrefreplace')`: characters beyond ASCII as `&#N;`. */
const asciiRefs = (s: string): string => s.replace(/[\u{80}-\u{10FFFF}]/gu, (c) => `&#${Number(c.codePointAt(0))};`);

// ---------------------------------------------------------------------------
// Settings
// ---------------------------------------------------------------------------

/** Settings of the MathML printers (SymPy's MathMLPrinterBase settings in camelCase). */
export interface MathMLOptions {
  /** Rational powers in presentation MathML as bevelled fractions. */
  readonly foldFracPowers?: boolean;
  /** Short fractions in presentation MathML as bevelled fractions. */
  readonly foldShortFrac?: boolean;
  /** `ln` instead of `log` (presentation). */
  readonly lnNotation?: boolean;
  /** The delimiter of matrices in presentation MathML: '[' (default), '(' or '' for none. */
  readonly matDelim?: '[' | '(' | '';
  /** 'bold' prints matrix symbols in bold (presentation). */
  readonly matSymbolStyle?: 'plain' | 'bold';
  /** The multiplication symbol of presentation MathML: none (invisible times), 'times', 'dot', 'ldot' or any text. */
  readonly mulSymbol?: string;
  /** The symbol between the mantissa and the power of ten of a float (default a middle dot). */
  readonly mulSymbolMathmlNumbers?: string;
  /** Roots as roots (default true); false prints fractional powers. */
  readonly rootNotation?: boolean;
  /** Prints symbol names as they are, without sub- and superscripts. */
  readonly disableSplitSuperSub?: boolean;
}

interface Settings {
  readonly foldFracPowers: boolean;
  readonly foldShortFrac: boolean;
  readonly lnNotation: boolean;
  readonly matDelim: '[' | '(' | '';
  readonly matSymbolStyle: 'plain' | 'bold';
  readonly mulSymbol: string | undefined;
  readonly mulSymbolMathmlNumbers: string;
  readonly rootNotation: boolean;
  readonly disableSplitSuperSub: boolean;
}

const MATHML_SETTINGS = new Set(['foldFracPowers', 'foldShortFrac', 'lnNotation', 'matDelim', 'matSymbolStyle', 'mulSymbol', 'mulSymbolMathmlNumbers', 'rootNotation', 'disableSplitSuperSub', 'printer']);

/** SymPy MathMLPrinterBase.__init__: the settings with their defaults (an unknown setting is a TypeError). */
function resolve(o: MathMLOptions): Settings {
  for (const k of Object.keys(o)) if (!MATHML_SETTINGS.has(k)) throw new TypeError(`Unknown setting '${k}'.`);
  return resolveKnown(o);
}

const resolveKnown = (o: MathMLOptions): Settings => ({
  foldFracPowers: o.foldFracPowers ?? false,
  foldShortFrac: o.foldShortFrac ?? false,
  lnNotation: o.lnNotation ?? false,
  matDelim: o.matDelim ?? '[',
  matSymbolStyle: o.matSymbolStyle ?? 'plain',
  mulSymbol: o.mulSymbol,
  mulSymbolMathmlNumbers: o.mulSymbolMathmlNumbers ?? '&#xB7;',
  rootNotation: o.rootNotation ?? true,
  disableSplitSuperSub: o.disableSplitSuperSub ?? false,
});

/** A matrix as the MathML printers see it (the matrices layer is above this one). */
export interface MathMLMatrix {
  readonly rows: number;
  readonly cols: number;
  get(i: number, j: number): Expr;
}

/** What the MathML printers print: expressions (numbers are sympified), matrices and lists. */
export type MathMLPrintable = Expr | number | bigint | boolean | MathMLMatrix | readonly MathMLPrintable[];

const isList = (v: MathMLPrintable): v is readonly MathMLPrintable[] => Array.isArray(v);

// ---------------------------------------------------------------------------
// Helpers shared by the two printers
// ---------------------------------------------------------------------------

const isExp = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

/** SymPy's class name of a node that is not a number or a symbol (the function name, Add, And, Union, ...). */
function className(e: Expr): string {
  if (e instanceof BoolOp) return e.className;
  return setClass(e) ?? sympyClassName(e);
}

/** SymPy `fraction(expr)` (not exact): the numerator and the denominator of a product. */
function fraction(e: Expr): [Expr, Expr] {
  const numer: Expr[] = [];
  const denom: Expr[] = [];
  for (const t of e instanceof Mul ? e.args : [e]) {
    if (t instanceof Pow && t.isCommutative) {
      const x = t.exp;
      // a negative power, or one whose exponent extracts a minus sign, is in the denominator
      if (isNegative(x) === true || (x instanceof Mul && startsNegative(x))) denom.push(x instanceof Rational && x.p === -1n && x.q === 1n ? t.base : impl.pow(t.base, impl.mul(-1, x)));
      else numer.push(t);
    } else if (t instanceof Rational && !t.isInteger) {
      if (t.p !== 1n) numer.push(Rational.of(t.p));
      denom.push(Rational.of(t.q));
    } else numer.push(t);
  }
  const prod = (fs: Expr[]): Expr => (fs.length === 0 ? Rational.of(1n) : fs.length === 1 ? at(fs, 0) : new Mul(fs));
  return [prod(numer), prod(denom)];
}

const isOne = (e: Expr): boolean => e instanceof Rational && e.p === 1n && e.q === 1n;

/** The integrand and the limits of nested integrals (SymPy keeps them in one Integral, innermost first). */
function integralLimits(e: Integral): [Expr, Expr[][]] {
  const limits: Expr[][] = [];
  let cur: Expr = e;
  while (cur instanceof Integral) {
    const lim = cur.limits;
    limits.push(lim ? [cur.variable, ...lim] : [cur.variable]);
    cur = cur.integrand;
  }
  return [cur, limits.reverse()];
}

// ---------------------------------------------------------------------------
// Content MathML
// ---------------------------------------------------------------------------

const CONTENT_TAGS: Readonly<Record<string, string>> = {
  Add: 'plus', Mul: 'times', Derivative: 'diff', Number: 'cn', int: 'cn', Pow: 'power', Max: 'max', Min: 'min', Abs: 'abs',
  And: 'and', Or: 'or', Xor: 'xor', Not: 'not', Implies: 'implies', Symbol: 'ci', MatrixSymbol: 'ci', RandomSymbol: 'ci',
  Integral: 'int', Sum: 'sum', sin: 'sin', cos: 'cos', tan: 'tan', cot: 'cot', csc: 'csc', sec: 'sec', sinh: 'sinh', cosh: 'cosh',
  tanh: 'tanh', coth: 'coth', csch: 'csch', sech: 'sech', asin: 'arcsin', asinh: 'arcsinh', acos: 'arccos', acosh: 'arccosh',
  atan: 'arctan', atanh: 'arctanh', atan2: 'arctan', acot: 'arccot', acoth: 'arccoth', asec: 'arcsec', asech: 'arcsech',
  acsc: 'arccsc', acsch: 'arccsch', log: 'ln', Equality: 'eq', Unequality: 'neq', GreaterThan: 'geq', LessThan: 'leq',
  StrictGreaterThan: 'gt', StrictLessThan: 'lt', Union: 'union', Intersection: 'intersect',
};

/** SymPy `mathml_tag` of a node that is not a number or a symbol: the tag of its class, else the lowercased class name. */
function mathmlTag(e: Expr, table: Readonly<Record<string, string>>): string {
  const cls = className(e);
  return table[cls] ?? cls.toLowerCase();
}

/** The sub- and superscripts of a symbol name (SymPy `_split_super_sub` and greek letters as unicode). */
function symbolParts(name0: string, s: Settings): [string, string[], string[]] {
  const [name, supers, subs] = s.disableSplitSuperSub ? [name0, [], []] : splitSuperSub(name0);
  const tr = (t: string): string => greekUnicode.get(t) ?? t;
  return [tr(name), supers.map(tr), subs.map(tr)];
}

/** SymPy MathMLContentPrinter. */
class ContentPrinter {
  constructor(readonly s: Settings) {}

  print(v: MathMLPrintable): MathMLElement {
    if (typeof v === 'boolean') return this.expr(new BoolAtom(v));
    if (typeof v === 'number' || typeof v === 'bigint') return this.expr(sympify(v));
    if (isList(v)) return el('list', ...v.map((x) => this.print(x)));
    if (v instanceof Expr) return this.expr(v);
    const m = el('matrix');
    for (let i = 0; i < v.rows; i++) {
      const row = el('matrixrow');
      for (let j = 0; j < v.cols; j++) row.append(this.expr(v.get(i, j)));
      m.append(row);
    }
    return m;
  }

  private tag(e: Expr): string {
    return mathmlTag(e, CONTENT_TAGS);
  }

  private apply(head: string, ...args: (MathMLElement | string)[]): MathMLElement {
    return el('apply', el(head), ...args);
  }

  expr(e: Expr): MathMLElement {
    if (e instanceof Rational) {
      if (e.q === 1n) return el('cn', String(e.p));
      return this.apply('divide', el('cn', String(e.p)), el('cn', String(e.q)));
    }
    if (e instanceof Float) return el('cn', toStr(e.mpf, precToDps(e.prec) === 15 ? 17 : precToDps(e.prec) + 3));
    if (e instanceof Constant) {
      const named: Partial<Record<string, string>> = { I: 'imaginaryi', EulerGamma: 'eulergamma', E: 'exponentiale', pi: 'pi' };
      const tag = named[e.name];
      if (tag !== undefined) return el(tag);
      // SymPy prints GoldenRatio as phi; the other constants as their class name
      return e.name === 'GoldenRatio' ? el('cn', 'φ') : el(this.tag(e));
    }
    if (e instanceof Special) {
      if (e.name === 'oo') return el('infinity');
      if (e.name === '-oo') return this.apply('minus', el('infinity'));
      return el(e.name === 'nan' ? 'notanumber' : this.tag(e));
    }
    if (e instanceof BoolAtom) return el(e.value ? 'true' : 'false');
    if (e instanceof Sym) return this.symbol(e.name);
    if (e instanceof Add) return this.add(e);
    if (e instanceof Mul) return this.mul(e);
    if (e instanceof Pow && isExp(e)) return this.apply('exp', this.expr(e.exp));
    if (e instanceof Pow) return this.pow(e);
    if (e instanceof Rel) return this.apply(this.tag(e), this.expr(e.lhs), this.expr(e.rhs));
    if (e instanceof Piecewise) return this.piecewise(e);
    if (e instanceof Derivative) {
      const bvar = el('bvar');
      for (const [x, n] of [...e.variableOrders].reverse()) {
        bvar.append(this.expr(x));
        if (n.key !== '1') bvar.append(el('degree', this.expr(n)));
      }
      return this.apply(requiresPartial(e.expr) ? 'partialdiff' : 'diff', bvar, this.expr(e.expr));
    }
    if (e instanceof Integral) {
      const [f, limits] = integralLimits(e);
      return this.limits('int', f, limits);
    }
    if (e instanceof Concrete) {
      // SymPy prints a Sum like an integral and a Product with _print_Basic
      if (e.kind2 === 'Sum') return this.limits('sum', e.function, e.limits);
      return el('product', this.expr(e.function), ...e.limits.map((l) => el('tuple', ...l.map((x) => this.expr(x)))));
    }
    if (e instanceof Limit) return this.apply('limit', el('bvar', this.expr(e.variable)), el('lowlimit', this.expr(e.point)), this.expr(e.expr));
    if (e instanceof BoolOp) return this.apply(this.tag(e), ...e.args.map((a) => this.expr(a)));
    if (e instanceof Fn || e instanceof UndefFn) return this.apply(this.tag(e), ...e.args.map((a) => this.expr(a)));
    const cls = setClass(e);
    if (cls === 'EmptySet') return el('emptyset');
    if (cls === 'FiniteSet') return el('set', ...e.args.map((a) => this.expr(a)));
    if (cls === 'Complement') return this.apply('setdiff', ...e.args.map((a) => this.expr(a)));
    if (cls === 'ProductSet') return this.apply('cartesianproduct', ...e.args.map((a) => this.expr(a)));
    if (cls === 'Union' || cls === 'Intersection') return this.apply(this.tag(e), ...setArgsOrdered(e.args).map((a) => this.expr(a)));
    if (e instanceof ExtensionExpr && e.name === 'MatrixSymbol') return this.symbol(str(e));
    if (e instanceof ExtensionExpr && e.name === 'Lambda') {
      const vars = e.args.slice(0, -1).map((a) => el('bvar', this.expr(a)));
      return el('lambda', ...vars, this.expr(at(e.args, e.args.length - 1)));
    }
    // SymPy _print_Basic: the lowercased class name around the arguments
    return el(this.tag(e), ...e.args.map((a) => this.expr(a)));
  }

  private symbol(text: string): MathMLElement {
    const [name, supers, subs] = symbolParts(text, this.s);
    const join = (items: string[]): MathMLElement => {
      if (items.length === 1) return el('mml:mi', at(items, 0));
      const row = el('mml:mrow');
      items.forEach((t, i) => {
        if (i > 0) row.append(el('mml:mo', ' '));
        row.append(el('mml:mi', t));
      });
      return row;
    };
    const ci = el('ci');
    const mname = el('mml:mi', name);
    if (supers.length === 0) return subs.length === 0 ? ci.append(name) : ci.append(el('mml:msub', mname, join(subs)));
    return ci.append(subs.length === 0 ? el('mml:msup', mname, join(supers)) : el('mml:msubsup', mname, join(subs), join(supers)));
  }

  private add(e: Expr): MathMLElement {
    const args = asOrderedTerms(e);
    let last = this.expr(at(args, 0));
    const plusNodes: MathMLElement[] = [];
    args.slice(1).forEach((arg, k) => {
      const isLast = k === args.length - 2;
      if (startsNegative(arg)) {
        last = this.apply('minus', last, this.expr(impl.mul(-1, arg)));
        if (isLast) plusNodes.push(last);
      } else {
        plusNodes.push(last);
        last = this.expr(arg);
        if (isLast) plusNodes.push(this.expr(arg));
      }
    });
    if (plusNodes.length === 1) return last;
    return this.apply('plus', ...plusNodes);
  }

  private mul(e: Mul): MathMLElement {
    if (startsNegative(e)) return this.apply('minus', this.mulNode(impl.mul(-1, e)));
    return this.mulNode(e);
  }

  private mulNode(e: Expr): MathMLElement {
    if (!(e instanceof Mul)) return this.expr(e);
    const [numer, denom] = fraction(e);
    if (!isOne(denom)) return this.apply('divide', this.expr(numer), this.expr(denom));
    const [coeff, rest] = splitCoeff(e);
    const terms = rest instanceof Mul ? asOrderedFactors(rest) : [rest];
    return this.apply('times', ...(isOne(coeff) ? [] : [this.expr(coeff)]), ...terms.map((t) => this.expr(t)));
  }

  private pow(e: Pow): MathMLElement {
    const x = e.exp;
    if (this.s.rootNotation && x instanceof Rational && x.p === 1n) {
      const degree = x.q === 2n ? [] : [el('degree', el('cn', String(x.q)))];
      return this.apply('root', ...degree, this.expr(e.base));
    }
    return this.apply('power', this.expr(e.base), this.expr(x));
  }

  private piecewise(e: Piecewise): MathMLElement {
    const pairs = e.pairs;
    const lastCond = at(pairs, pairs.length - 1)[1];
    if (!(lastCond instanceof BoolAtom && lastCond.value)) {
      throw new RangeError('All Piecewise expressions must contain an (expr, True) statement to be used as a default condition. Without one, the generated expression may not evaluate to anything under some condition.');
    }
    return el(
      'piecewise',
      ...pairs.map(([x, c], i) => (i === pairs.length - 1 ? el('otherwise', this.expr(x)) : el('piece', this.expr(x), this.expr(c)))),
    );
  }

  /** SymPy `_print_Integral` (also of Sum): nested applications, outermost limits first. */
  private limits(head: string, f: Expr, limits: readonly (readonly Expr[])[]): MathMLElement {
    const ls = [...limits].reverse();
    const rec = (k: number): MathMLElement => {
      const l = at(ls, k);
      const x = this.apply(head, el('bvar', this.expr(at(l, 0))));
      if (l.length === 3) x.append(el('lowlimit', this.expr(at(l, 1))), el('uplimit', this.expr(at(l, 2))));
      return x.append(k === ls.length - 1 ? this.expr(f) : rec(k + 1));
    };
    return rec(0);
  }
}

// ---------------------------------------------------------------------------
// Presentation MathML
// ---------------------------------------------------------------------------

const PRESENTATION_TAGS: Readonly<Record<string, string>> = {
  Number: 'mn', Limit: '&#x2192;', Derivative: '&dd;', int: 'mn', Symbol: 'mi', Integral: '&int;', Sum: '&#x2211;',
  sin: 'sin', cos: 'cos', tan: 'tan', cot: 'cot', asin: 'arcsin', asinh: 'arcsinh', acos: 'arccos', acosh: 'arccosh',
  atan: 'arctan', atanh: 'arctanh', acot: 'arccot', atan2: 'arctan', Equality: '=', Unequality: '&#x2260;',
  GreaterThan: '&#x2265;', LessThan: '&#x2264;', StrictGreaterThan: '>', StrictLessThan: '<', lerchphi: '&#x3A6;',
  zeta: '&#x3B6;', dirichlet_eta: '&#x3B7;', elliptic_k: '&#x39A;', lowergamma: '&#x3B3;', uppergamma: '&#x393;',
  gamma: '&#x393;', totient: '&#x3D5;', reduced_totient: '&#x3BB;', primenu: '&#x3BD;', primeomega: '&#x3A9;',
  fresnels: 'S', fresnelc: 'C', LambertW: 'W', Heaviside: '&#x398;', BooleanTrue: 'True', BooleanFalse: 'False',
  NoneType: 'None', mathieus: 'S', mathieuc: 'C', mathieusprime: 'S&#x2032;', mathieucprime: 'C&#x2032;', Lambda: 'lambda',
};

/** SymPy `precedence_traditional`. */
const precedence = (e: Expr): number => {
  if (e instanceof ExtensionExpr && e.name === 'VectorAdd') return PREC.ADD;
  if (e instanceof ExtensionExpr && e.name === 'VectorMul') return PREC.MUL;
  if (e instanceof Integral || e instanceof Concrete) return PREC.MUL;
  return declaredPrecedence(e, 'latexPrecedence') ?? strPrecedence(e);
};

const PRESENTATION_CONSTANTS: Readonly<Record<string, string>> = {
  I: '&ImaginaryI;', GoldenRatio: '&#x3A6;', E: '&ExponentialE;', pi: '&pi;', EulerGamma: '&#x3B3;', TribonacciConstant: 'TribonacciConstant',
};
const NAMED_SETS: Readonly<Record<string, string>> = { Integers: '&#x2124;', Complexes: '&#x2102;', Reals: '&#x211D;', Naturals: '&#x2115;' };
const NUMBER_FUNCTIONS: Readonly<Record<string, string>> = { bernoulli: 'B', bell: 'B', catalan: 'C', euler: 'E', fibonacci: 'F', lucas: 'L', stieltjes: '&#x03B3;', tribonacci: 'T' };
const SET_OPS: Readonly<Record<string, string>> = { Union: '&#x222A;', Intersection: '&#x2229;', Complement: '&#x2216;', SymmetricDifference: '&#x2206;', ProductSet: '&#x00d7;' };
const LOG_OPS: Readonly<Record<string, string>> = { And: '&#x2227;', Or: '&#x2228;', Xor: '&#x22BB;', Implies: '&#x21D2;', Equivalent: '&#x21D4;' };

const mo = (t: string): MathMLElement => el('mo', t);
const mi = (t: string): MathMLElement => el('mi', t);
const sortedArgs = (args: readonly Expr[]): Expr[] => [...args].sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
/** SymPy `is_Boolean`: a boolean function or atom (a relation is not one). */
const isBoolean = (e: Expr): boolean => e instanceof BoolOp || e instanceof BoolAtom;

/** Coordinate basis nodes expose their index and coordinate system to the printers. */
interface BasisNode extends Expr {
  readonly index: number;
  readonly system: { readonly sysName: string; readonly vectorNames: readonly string[]; readonly variableNames: readonly string[] };
}
const isBasisNode = (e: Expr): e is BasisNode => e instanceof Sym ? e.sortClass === 'BaseScalar' : e instanceof ExtensionExpr && e.name === 'BaseVector';

const isComponentVector = (e: Expr): e is ExtensionExpr & { readonly components: Iterable<readonly [Expr, Expr]> } => e instanceof ExtensionExpr && (e.name === 'VectorAdd' || e.name === 'VectorMul');

/** SymPy MathMLPresentationPrinter. */
class PresentationPrinter {
  constructor(readonly s: Settings) {}

  print(v: MathMLPrintable): MathMLElement {
    if (typeof v === 'boolean') return this.expr(new BoolAtom(v));
    if (typeof v === 'number' || typeof v === 'bigint') return this.expr(sympify(v));
    // SymPy prints a list like a tuple (_print_list is not defined: the tuple printer of the base printer)
    if (isList(v)) return this.parenComma(v.map((x) => this.print(x)));
    if (v instanceof Expr) return this.expr(v);
    return this.matrix(v);
  }

  private tag(e: Expr): string {
    if (e instanceof Mul) {
      const m = this.s.mulSymbol;
      if (m === undefined || m === 'None') return '&InvisibleTimes;';
      return ({ times: '&#xD7;', dot: '&#xB7;', ldot: '&#x2024;' } as Partial<Record<string, string>>)[m] ?? m;
    }
    return mathmlTag(e, PRESENTATION_TAGS);
  }

  private parenComma(items: readonly MathMLElement[], sep = ','): MathMLElement {
    const row = el('mrow', mo('('));
    items.forEach((x, i) => {
      if (i) row.append(mo(sep));
      row.append(x);
    });
    return row.append(mo(')'));
  }

  private parenthesize(e: Expr, level: number, strict = false): MathMLElement {
    const p = precedence(e);
    if (p < level || (!strict && p <= level)) return el('mrow', mo('('), this.expr(e), mo(')'));
    return this.expr(e);
  }

  private matrix(m: MathMLMatrix): MathMLElement {
    const table = el('mtable');
    for (let i = 0; i < m.rows; i++) {
      const row = el('mtr');
      for (let j = 0; j < m.cols; j++) row.append(el('mtd', this.expr(m.get(i, j))));
      table.append(row);
    }
    const d = this.s.matDelim;
    if (d === '') return table;
    return el('mrow', mo(d), table, mo(d === '[' ? ']' : ')'));
  }

  /** SymPy `_get_printed_Rational`. */
  private rational(e: Rational, folded: boolean): MathMLElement {
    const frac = el('mfrac');
    if (folded || this.s.foldShortFrac) frac.set('bevelled', 'true');
    frac.append(this.expr(Rational.of(e.p < 0n ? -e.p : e.p)), this.expr(Rational.of(e.q)));
    return e.p < 0n ? el('mrow', mo('-'), frac) : frac;
  }

  expr(e: Expr): MathMLElement {
    if (isBasisNode(e)) {
      const vector = e instanceof ExtensionExpr;
      const bold = (name: string): MathMLElement => mi(name).set('mathvariant', 'bold');
      const name = bold(at(vector ? e.system.vectorNames : e.system.variableNames, e.index));
      return el('msub', vector ? el('mover', name, mo('^')) : name, bold(e.system.sysName));
    }
    if (e instanceof ExtensionExpr) {
      if (e.name === 'VectorZero') return el('mover', mi('0').set('mathvariant', 'bold'), mo('^'));
      if (isComponentVector(e)) {
        const row = el('mrow');
        const components = [...e.components].sort(([a], [b]) => Number(str(a) > str(b)) - Number(str(a) < str(b)));
        components.forEach(([basis, coeff], i) => {
          if (coeff instanceof Rational && coeff.p === -1n && coeff.q === 1n) row.append(mo('-'), this.expr(basis));
          else {
            if (i) row.append(mo('+'));
            if (!isOne(coeff)) row.append(el('mrow', mo('('), this.expr(coeff), mo(')')), mo('&InvisibleTimes;'));
            row.append(this.expr(basis));
          }
        });
        return row;
      }
      if (e.name === 'Cross' || e.name === 'Dot') return el('mrow', this.parenthesize(at(e.args, 0), PREC.MUL), mo(e.name === 'Cross' ? '&#xD7;' : '&#xB7;'), this.parenthesize(at(e.args, 1), PREC.MUL));
      if (['Curl', 'Divergence', 'Gradient', 'Laplacian'].includes(e.name)) {
        const row = el('mrow', mo(e.name === 'Laplacian' ? '&#x2206;' : '&#x2207;'));
        if (e.name === 'Curl' || e.name === 'Divergence') row.append(mo(e.name === 'Curl' ? '&#xD7;' : '&#xB7;'));
        return row.append(this.parenthesize(at(e.args, 0), PREC.MUL));
      }
    }

    if (e instanceof Rational) return e.q === 1n ? el('mn', String(e.p)) : this.rational(e, this.s.foldShortFrac);
    if (e instanceof Float) return this.float(e);
    if (e instanceof Constant) {
      const c = PRESENTATION_CONSTANTS[e.name];
      // SymPy _print_Basic for the other constants (Catalan)
      if (c === undefined) return el('mrow', mi(this.tag(e).toLowerCase()), this.parenComma([]));
      return mi(c);
    }
    if (e instanceof Special) {
      if (e.name === 'oo') return mi('&#x221E;');
      if (e.name === '-oo') return el('mrow', mo('-'), mi('&#x221E;'));
      if (e.name === 'zoo') return el('mover', mo('&#x221E;'), mo('~'));
      return mi('NaN');
    }
    if (e instanceof BoolAtom) return mi(e.value ? 'True' : 'False');
    if (e instanceof Sym) return this.symbol(e.name, 'plain');
    if (e instanceof Add) return this.add(e);
    if (e instanceof Mul) return startsNegative(e) ? this.multiply(impl.mul(-1, e), el('mrow', mo('-'))) : this.multiply(e, el('mrow'));
    if (e instanceof Pow && isExp(e)) return el('msup', mi('&ExponentialE;'), this.expr(e.exp));
    if (e instanceof Pow) return this.pow(e);
    if (e instanceof Rel) return el('mrow', this.expr(e.lhs), mo(this.tag(e)), this.expr(e.rhs));
    if (e instanceof Derivative) return this.derivative(e);
    if (e instanceof Integral) return this.integral(e);
    if (e instanceof Concrete) return this.sum(e);
    if (e instanceof Limit) return el('mrow', el('munder', mi('lim'), el('mrow', this.expr(e.variable), mo(this.tag(e)), this.expr(e.point))), this.expr(e.expr));
    if (e instanceof BoolOp) return this.logic(e);
    if (e instanceof Fn || e instanceof ExtensionExpr) {
      const named = this.namedFunction(e.name, e.args);
      if (named) return named;
    }
    if (e instanceof Fn || e instanceof UndefFn) return this.func(e);
    // SymPy _print_Basic, the pieces (ExprCondPair) being tuples
    if (e instanceof Piecewise) return el('mrow', mi('piecewise'), this.parenComma(e.pairs.map(([x, c]) => this.parenComma([this.expr(x), this.expr(c)]))));
    const s = this.set(e);
    if (s) return s;
    if (e instanceof ExtensionExpr) {
      if (e.name === 'Tuple') return this.parenComma(e.args.map((a) => this.expr(a)));
      if (e.name === 'Lambda') {
        const vars = e.args.slice(0, -1);
        const v = vars.length === 1 ? this.expr(at(vars, 0)) : this.parenComma(vars.map((a) => this.expr(a)));
        return el('mrow', mo('('), v, mo('&#x21A6;'), this.expr(at(e.args, e.args.length - 1)), mo(')'));
      }
      if (e.name === 'MatrixSymbol') return this.symbol(str(e), this.s.matSymbolStyle);
      const m = this.matrixExpr(e);
      if (m) return m;
    }
    // SymPy _print_Basic: the lowercased class name and the arguments in parentheses
    return el('mrow', mi(this.tag(e)), this.parenComma(e.args.map((a) => this.expr(a))));
  }

  /**
   * SymPy's printers of the matrix expressions and of Indexed (nodes of
   * higher layers, recognized by their class name); undefined for the others.
   */
  private matrixExpr(e: ExtensionExpr): MathMLElement | undefined {
    const args = e.args;
    const a0 = (): Expr => at(args, 0);
    // a matrix symbol as it is, anything else in parentheses (SymPy _print_Transpose, _print_MatPow, ...)
    const base = (x: Expr): MathMLElement => (x instanceof ExtensionExpr && x.name === 'MatrixSymbol' ? this.expr(x) : el('mrow', mo('('), this.expr(x), mo(')')));
    const joined = (xs: readonly Expr[], op: string): MathMLElement => {
      const row = el('mrow');
      xs.forEach((x, i) => {
        if (i) row.append(mo(op));
        row.append(this.parenthesize(x, precedence(e)));
      });
      return row;
    };
    switch (e.name) {
      case 'Transpose':
        return el('msup', base(a0()), mo('T'));
      case 'Adjoint':
        return el('msup', base(a0()), mo('&#x2020;'));
      case 'Inverse':
      case 'MatPow':
        return el('msup', base(a0()), this.expr(at(args, 1)));
      case 'MatAdd':
        return this.add(e);
      case 'MatMul': {
        const first = a0();
        let factors = first instanceof Mul ? [...asOrderedFactors(first), ...args.slice(1)] : [...args];
        const lead = at(factors, 0);
        const negative = isNum(lead) && lead.isNegative;
        if (negative) factors = lead instanceof Rational && lead.p === -1n && lead.q === 1n ? factors.slice(1) : [impl.mul(-1, lead), ...factors.slice(1)];
        const row = joined(factors, '&InvisibleTimes;');
        return negative ? el('mrow', mo('-'), ...row.children) : row;
      }
      case 'HadamardProduct':
        return joined(args, '&#x2218;');
      case 'Identity':
        return mi('&#x1D540;');
      case 'ZeroMatrix':
        return el('mn', '&#x1D7D8');
      case 'OneMatrix':
        return el('mn', '&#x1D7D9');
      case 'MatrixElement': {
        const parent = a0();
        const sub = el('mrow');
        args.slice(1).forEach((x, i) => {
          if (i) sub.append(mo(','));
          sub.append(this.expr(x));
        });
        return el('msub', this.parenthesize(parent, PREC.ATOM, true), sub);
      }
      case 'IndexedBase':
        return this.expr(a0());
      case 'Indexed': {
        const indices = args.slice(1);
        return el('msub', this.expr(a0()), indices.length === 1 ? this.expr(at(indices, 0)) : this.parenComma(indices.map((x) => this.expr(x))));
      }
      default:
        return undefined;
    }
  }

  private float(e: Float): MathMLElement {
    const s = toStr(e.mpf, precToDps(e.prec));
    const k = s.indexOf('e');
    if (k < 0) return el('mn', s);
    const exp = s.slice(k + 1).replace(/^\+/, '');
    return el('mrow', el('mn', s.slice(0, k)), mo(this.s.mulSymbolMathmlNumbers), el('msup', el('mn', '10'), el('mn', exp)));
  }

  private symbol(name0: string, style: 'plain' | 'bold'): MathMLElement {
    const [name, supers, subs] = symbolParts(name0, this.s);
    const join = (items: string[]): MathMLElement => {
      if (items.length === 1) return mi(at(items, 0));
      const row = el('mrow');
      items.forEach((t, i) => {
        if (i > 0) row.append(mo(' '));
        row.append(mi(t));
      });
      return row;
    };
    const mname = mi(name);
    let x: MathMLElement;
    if (supers.length === 0) x = subs.length === 0 ? mname : el('msub', mname, join(subs));
    else x = subs.length === 0 ? el('msup', mname, join(supers)) : el('msubsup', mname, join(subs), join(supers));
    if (style === 'bold') x.set('mathvariant', 'bold');
    return x;
  }

  private add(e: Expr): MathMLElement {
    const args = asOrderedTerms(e);
    const row = el('mrow', this.expr(at(args, 0)));
    for (const arg of args.slice(1)) {
      if (startsNegative(arg)) row.append(mo('-'), this.expr(impl.mul(-1, arg)));
      else row.append(mo('+'), this.expr(arg));
    }
    return row;
  }

  private multiply(e: Expr, row: MathMLElement): MathMLElement {
    const [numer, denom] = fraction(e);
    if (!isOne(denom)) {
      const frac = el('mfrac');
      if (this.s.foldShortFrac && str(e).length < 7) frac.set('bevelled', 'true');
      return row.append(frac.append(this.expr(numer), this.expr(denom)));
    }
    const [coeff, rest] = splitCoeff(e);
    const terms = rest instanceof Mul ? asOrderedFactors(rest) : [rest];
    if (isOne(coeff) && terms.length === 1) return row.append(this.expr(at(terms, 0)));
    const times = this.tag(new Mul([coeff, rest]));
    if (!isOne(coeff)) row.append(this.expr(coeff), mo(times));
    terms.forEach((t, i) => {
      row.append(this.parenthesize(t, PREC.MUL));
      if (i < terms.length - 1) row.append(mo(times));
    });
    return row;
  }

  private pow(e: Pow): MathMLElement {
    const x = e.exp;
    const base = (): MathMLElement => this.parenthesize(e.base, PREC.POW);
    if (x instanceof Rational && (x.p === 1n || x.p === -1n) && x.q !== 1n && this.s.rootNotation) {
      const root = x.q === 2n ? el('msqrt', this.expr(e.base)) : el('mroot', this.expr(e.base), this.expr(Rational.of(x.q)));
      return x.p === -1n ? el('mfrac', this.expr(Rational.of(1n)), root) : root;
    }
    if (x instanceof Rational && x.q !== 1n) {
      if (x.p < 0n) return el('mfrac', this.expr(Rational.of(1n)), el('msup', base(), this.rational(Rational.of(-x.p, x.q), this.s.foldFracPowers)));
      return el('msup', base(), this.rational(x, this.s.foldFracPowers));
    }
    if (isNegative(x) === true) {
      const top = el('mfrac', this.expr(Rational.of(1n)));
      if (x instanceof Rational && x.p === -1n) return top.append(this.expr(e.base));
      return top.append(el('msup', base(), this.expr(impl.mul(-1, x))));
    }
    return el('msup', base(), this.expr(x));
  }

  private derivative(e: Derivative): MathMLElement {
    const d = requiresPartial(e.expr) ? '&#x2202;' : '&dd;';
    const op = (n: Expr): MathMLElement => (n.key === '1' ? mo(d) : el('msup', mo(d), this.expr(n)));
    const den = el('mrow');
    for (const [x, n] of [...e.variableOrders].reverse()) den.append(op(n), this.expr(x));
    return el('mrow', el('mfrac', el('mrow', op(e.derivativeOrder)), den), this.expr(e.expr));
  }

  private integral(e: Integral): MathMLElement {
    const symbols = ['', '&#x222B;', '&#x222C;', '&#x222D;'];
    const [f, limits] = integralLimits(e);
    const row = el('mrow');
    if (limits.length <= 3 && limits.every((l) => l.length === 1)) row.append(mo(at(symbols, limits.length)));
    else {
      for (const lim of [...limits].reverse()) {
        const sign = mo('&#x222B;');
        row.append(lim.length === 3 ? el('msubsup', sign, this.expr(at(lim, 1)), this.expr(at(lim, 2))) : sign);
      }
    }
    row.append(this.parenthesize(f, PREC.MUL, true));
    for (const lim of [...limits].reverse()) row.append(mo('&dd;'), this.expr(at(lim, 0)));
    return row;
  }

  private sum(e: Concrete): MathMLElement {
    if (e.kind2 === 'Product') {
      // SymPy _print_Basic: the class name and the arguments (the limits as tuples)
      const args = [this.expr(e.function), ...e.limits.map((l) => this.parenComma(l.map((x) => this.expr(x))))];
      return el('mrow', mi('product'), this.parenComma(args));
    }
    const [k, a, b] = at(e.limits, 0);
    const under = el('munderover', mo('&#x2211;'), el('mrow', this.expr(k), mo('='), this.expr(a)), this.expr(b));
    return el('mrow', under, this.parenthesize(e.function, precedence(e)));
  }

  private logic(e: BoolOp): MathMLElement {
    const cls = e.className;
    if (cls === 'Not') {
      const a = at(e.args, 0);
      return el('mrow', mo('&#xAC;'), isBoolean(a) ? el('mrow', mo('('), this.expr(a), mo(')')) : this.expr(a));
    }
    const symbol = LOG_OPS[cls];
    // SymPy _print_Basic for ITE
    if (symbol === undefined) return el('mrow', mi(cls.toLowerCase()), this.parenComma(e.args.map((a) => this.expr(a))));
    const args = cls === 'Implies' ? e.args : sortedArgs(e.args);
    const item = (a: Expr): MathMLElement => (isBoolean(a) && !(a instanceof BoolOp && a.className === 'Not') ? el('mrow', mo('('), this.expr(a), mo(')')) : this.expr(a));
    const row = el('mrow', item(at(args, 0)));
    for (const a of args.slice(1)) row.append(mo(symbol), item(a));
    return row;
  }

  /**
   * SymPy's printers of the orthogonal polynomials, expint, the elliptic
   * integrals, Ei and SingularityFunction (function nodes here and extension
   * nodes in higher layers); undefined for the other names.
   */
  private namedFunction(name: string, args: readonly Expr[]): MathMLElement | undefined {
    const items = (xs: readonly Expr[]): MathMLElement => this.parenComma(xs.map((a) => this.expr(a)));
    const a0 = (): MathMLElement => this.expr(at(args, 0));
    const letters: Partial<Record<string, readonly [string, number]>> = {
      jacobi: ['P', 3], gegenbauer: ['C', 2], assoc_legendre: ['P', 2], assoc_laguerre: ['L', 2],
      chebyshevt: ['T', 1], chebyshevu: ['U', 1], legendre: ['P', 1], laguerre: ['L', 1], hermite: ['H', 1], expint: ['E', 1],
    };
    const letter = letters[name];
    if (letter !== undefined) {
      // SymPy _print_jacobi, _print_chebyshevt, ...: the letter, the degree below, the parameters above in parentheses
      const [head, k] = letter;
      const sub = k === 1 ? el('msub', mo(head), a0()) : el('msubsup', mo(head), a0(), items(args.slice(1, k)));
      return el('mrow', sub, items(args.slice(k)));
    }
    switch (name) {
      case 'elliptic_e':
      case 'elliptic_f':
        return el('mrow', mi(name === 'elliptic_e' ? '&#x1d5a4;' : '&#x1d5a5;'), this.parenComma(args.map((a) => this.expr(a)), '|'));
      case 'elliptic_pi': {
        const row = el('mrow', mo('('), a0());
        if (args.length === 3) row.append(mo(';'), this.expr(at(args, 1)));
        return el('mrow', mi('&#x1d6f1;'), row.append(mo('|'), this.expr(at(args, args.length - 1)), mo(')')));
      }
      case 'Ei':
        return el('mrow', mi('Ei'), items(args));
      case 'SingularityFunction': {
        const shift = impl.add(at(args, 0), impl.mul(-1, at(args, 1)));
        return el('msup', el('mrow', mo('\u27e8'), this.expr(shift), mo('\u27e9')), this.expr(at(args, 2)));
      }
      default:
        return undefined;
    }
  }

  private func(e: Fn | UndefFn): MathMLElement {
    const cls = className(e);
    const a0 = (): Expr => at(e.args, 0);
    const numberFn = NUMBER_FUNCTIONS[cls];
    if (numberFn !== undefined) {
      const sub = el('msub', mi(numberFn), this.expr(a0()));
      return e.args.length === 1 ? sub : el('mrow', sub, this.parenComma(e.args.slice(1).map((a) => this.expr(a))));
    }
    switch (cls) {
      case 'Abs':
        return el('mrow', mo('|'), this.expr(a0()), mo('|'));
      case 're':
      case 'im':
        return el('mrow', mi(cls === 're' ? 'ℜ' : 'ℑ'), el('mrow', mo('('), this.expr(a0()), mo(')')));
      case 'conjugate':
        return el('menclose', this.expr(a0())).set('notation', 'top');
      case 'factorial':
      case 'factorial2':
        return el('mrow', this.parenthesize(a0(), PREC.FUNC), mo(cls === 'factorial' ? '!' : '!!'));
      case 'binomial':
        return el('mrow', mo('('), el('mfrac', this.expr(a0()), this.expr(at(e.args, 1))).set('linethickness', '0'), mo(')'));
      case 'floor':
        return el('mrow', mo('⌊'), this.expr(a0()), mo('⌋'));
      case 'ceiling':
        return el('mrow', mo('⌈'), this.expr(a0()), mo('⌉'));
      case 'Min':
      case 'Max':
        return el('mrow', mo(cls.toLowerCase()), this.parenComma(sortedArgs(e.args).map((a) => this.expr(a))));
      case 'polylog':
        return el('mrow', el('msub', mi('Li'), this.expr(a0())), el('mrow', mo('('), this.expr(at(e.args, 1)), mo(')')));
      default: {
        const tag = this.tag(e);
        return el('mrow', mi(tag === 'log' && this.s.lnNotation ? 'ln' : tag), this.parenComma(e.args.map((a) => this.expr(a))));
      }
    }
  }

  private set(e: Expr): MathMLElement | undefined {
    const cls = setClass(e);
    if (cls === undefined) return undefined;
    const named = NAMED_SETS[cls];
    if (named !== undefined) return mi(named).set('mathvariant', 'normal');
    if (cls === 'Naturals0') return el('msub', mi('&#x2115;').set('mathvariant', 'normal'), this.expr(Rational.of(0n)));
    if (cls === 'EmptySet') return mo('&#x2205;');
    if (cls === 'Interval') {
      const open = (k: number): boolean => {
        const x = e.args[k];
        return x instanceof BoolAtom && x.value;
      };
      return el('mrow', mo(open(2) ? '(' : '['), this.expr(at(e.args, 0)), mo(','), this.expr(at(e.args, 1)), mo(open(3) ? ')' : ']'));
    }
    if (cls === 'FiniteSet') return this.braces(sortedArgs(e.args).map((a) => this.expr(a)));
    if (cls === 'Range') {
      const shown = rangePrintForm(e, 4);
      // a Range whose elements are unknown prints like any node
      if ('symbolic' in shown) return undefined;
      return this.braces(shown.elements.map((t) => (t === DOTS ? mi('\u2026') : this.expr(t))));
    }
    const op = SET_OPS[cls];
    if (op === undefined) return undefined;
    // SymPy keeps the sets of a union or an intersection sorted (by their infimum)
    const args = cls === 'Union' || cls === 'Intersection' ? setArgsOrdered(e.args) : e.args;
    const row = el('mrow', this.setOperand(at(args, 0)));
    for (const a of args.slice(1)) row.append(mo(op), this.setOperand(a));
    return row;
  }

  private braces(items: readonly MathMLElement[]): MathMLElement {
    const row = el('mrow', mo('{'));
    items.forEach((x, i) => {
      if (i) row.append(mo(','));
      row.append(x);
    });
    return row.append(mo('}'));
  }

  /** A set operation inside another one in parentheses (SymPy gives them all the precedence of Xor). */
  private setOperand(a: Expr): MathMLElement {
    const cls = setClass(a);
    return cls !== undefined && SET_OPS[cls] !== undefined ? el('mrow', mo('('), this.expr(a), mo(')')) : this.expr(a);
  }
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

/** The options of {@link mathml} and {@link printMathml}: the printer and its settings. */
export interface MathMLPrintOptions extends MathMLOptions {
  /** 'content' (default) or 'presentation' MathML. */
  readonly printer?: 'content' | 'presentation';
}

function element(expr: MathMLPrintable, options: MathMLPrintOptions): MathMLElement {
  const s = resolve(options);
  return options.printer === 'presentation' ? new PresentationPrinter(s).print(expr) : new ContentPrinter(s).print(expr);
}

/**
 * The MathML of an
 * expression, matrix or list on one line, characters beyond ASCII as
 * character references (`mathml(add(x, 1))` is
 * `<apply><plus/><ci>x</ci><cn>1</cn></apply>`).
 *
 * @param expr - The value to format.
 * @param options - The math mlprint settings.
 * @returns The MathML representation.
 * @see SymPy `sympy.printing.mathml.mathml`
 */
export function mathml(expr: MathMLPrintable, options: MathMLPrintOptions = {}): string {
  return asciiRefs(element(expr, options).toxml());
}

/**
 * Formats the MathML of an expression as indented XML.
 *
 * @param expr - The value to format.
 * @param options - The math mlprint settings.
 * @returns The MathML representation.
 * @see SymPy `sympy.printing.mathml.print_mathml`
 * @example
 * ```ts
 * import { ex, printMathml } from '@symjs/symjs';
 * printMathml(ex`x + 1`).trimEnd(); // => <apply>
 * //   	<plus/>
 * //   	<ci>x</ci>
 * //   	<cn>1</cn>
 * //   </apply>
 * ```
 */
export function printMathml(expr: MathMLPrintable, options: MathMLPrintOptions = {}): string {
  return `${element(expr, options).toprettyxml()}\n`;
}

/**
 * Prints an expression to the Content MathML markup language.
 *
 * @see SymPy `sympy.printing.mathml.MathMLContentPrinter`
 */
export class MathMLContentPrinter {
  /**
   * Creates a MathMLContentPrinter instance.
   *
   * @param settings - The math mloptions settings.
   */
  constructor(
    /** The formatting settings for this printer. */
    readonly settings: MathMLOptions = {}) {}
  /**
   * The content MathML of the expression.
   *
   * @param expr - The value to format.
   * @returns The formatted text.
   * @see SymPy `sympy.printing.mathml.MathMLContentPrinter.doprint`
   */
  doprint(expr: MathMLPrintable): string {
    return mathml(expr, { ...this.settings, printer: 'content' });
  }
}

/**
 * Prints an expression to the Presentation MathML markup language.
 *
 * @see SymPy `sympy.printing.mathml.MathMLPresentationPrinter`
 */
export class MathMLPresentationPrinter {
  /**
   * Creates a MathMLPresentationPrinter instance.
   *
   * @param settings - The math mloptions settings.
   */
  constructor(
    /** The formatting settings for this printer. */
    readonly settings: MathMLOptions = {}) {}
  /**
   * The presentation MathML of the expression.
   *
   * @param expr - The value to format.
   * @returns The formatted text.
   * @see SymPy `sympy.printing.mathml.MathMLPresentationPrinter.doprint`
   */
  doprint(expr: MathMLPrintable): string {
    return mathml(expr, { ...this.settings, printer: 'presentation' });
  }
}
