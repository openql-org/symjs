// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of SymPy's 2D pretty printer (`sympy.printing.pretty.pretty`):
 * `PrettyPrinter`, `pretty`, `pprint` / `pretty_print` and `pager_print`.
 *
 * The output matches SymPy 1.14 character for character, in unicode and in
 * ASCII mode:
 *
 * ```text
 *  2
 * x  + 2⋅x + 1
 * ```
 *
 * Nodes of higher layers are reached structurally (sets by their class
 * name, matrices by `rows`/`cols`/`get`), and extension nodes without a
 * dedicated rule print as `Name(args)` with pretty arguments, or through a
 * printer registered in {@link prettyHooks}.
 */

import {
  Add,
  Expr,
  BoolAtom,
  Constant,
  Derivative,
  Dummy,
  ExtensionExpr,
  Float,
  Fn,
  Integral,
  Limit,
  Mul,
  Order,
  Piecewise,
  Pow,
  Rational,
  Rel,
  S,
  Special,
  Sym,
  UndefFn,
  impl,
  isNum,
} from '../../core/nodes';
import { at, defined, getOrThrow, last } from '../../core/guard';
import { couldExtractMinusSign, splitCoeff } from '../../core/ops';
import { numNeg } from '../../core/num';
import { BoolOp } from '../../core/boolalg';
import { Concrete } from '../../core/concrete';
import { asOrderedFactors, asOrderedTerms, compareKeys, sortKey, sympyFunctionName } from '../sortkey';
import type { Key } from '../sortkey';
import { PREC, floatString, precedence, str } from '../str';
import { DOTS, rangePrintForm, setArgsOrdered, setClass } from '../sets';
import { hasSymbolicBounds, isSequence, sequencePrintset } from '../sequences';
import type { PictLike } from './stringpict';
import { Binding, LINE, PrettyForm, StringPict } from './stringpict';
import {
  annotated,
  centerPad,
  greekUnicode,
  hobj,
  nthRoot,
  prettyAtom,
  prettyMulSymbol,
  prettySymbol,
  prettyUseUnicode,
  sub,
  vobj,
  xsym,
} from './symbology';

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/** Settings of the pretty printer (SymPy's `PrettyPrinter` settings in camelCase). */
export interface PrettyOptions {
  /** Use unicode characters (default true; SymPy's default depends on the terminal). */
  readonly useUnicode?: boolean;
  /** Break lines longer than `numColumns` (default true). */
  readonly wrapLine?: boolean;
  /** Number of columns before line breaking (default 80). */
  readonly numColumns?: number;
  /** Term order of sums: 'lex' (SymPy's default) or 'none' (as stored). */
  readonly orderTerms?: 'lex' | 'none';
  /** Full precision of floats: 'auto' (default: only at top level), true or false. */
  readonly fullPrec?: boolean | 'auto';
  /**
   * The multiplication symbol; defaults to '⋅' in unicode and '*' in ASCII
   * (a symjs extension: SymPy's pretty printer has no such setting).
   */
  readonly mulSymbol?: string;
  /** Letter of the imaginary unit in unicode mode: 'i' (default, ⅈ) or 'j' (ⅉ). */
  readonly imaginaryUnit?: 'i' | 'j';
  /** Print exponents 1/n as roots (default true); false prints x**(1/3) as a power. */
  readonly rootNotation?: boolean;
  /** Use the single-character square root sign when unambiguous (default true). */
  readonly useUnicodeSqrtChar?: boolean;
  /** 'bold' prints matrix symbols in a bold face (used by matrix hooks; default 'plain'). */
  readonly matSymbolStyle?: 'plain' | 'bold';
}

/** A matrix as seen by the printer: anything with a shape and entries. */
export interface MatrixLike {
  readonly rows: number;
  readonly cols: number;
  get(i: number, j: number): Expr;
}

/** A Python-style tuple for the printer (JS arrays print as lists `[...]`). */
export class PrettyTuple {
  readonly items: readonly Printable[];
  constructor(...items: Printable[]) {
    this.items = items;
  }
}

/** Anything the pretty printer accepts. */
export type Printable =
  | Expr
  | number
  | bigint
  | string
  | boolean
  | StringPict
  | MatrixLike
  | PrettyTuple
  | readonly Printable[]
  | ReadonlyMap<Printable, Printable>;

/**
 * Printers for nodes defined in higher layers or extend packages, keyed by
 * the node's name (`ExtensionExpr.name`, or `'Matrix'` for matrices). A
 * higher layer fills these in when it is loaded.
 */
export const prettyHooks: {
  readonly extension: Map<string, (e: Expr, printer: PrettyPrinter) => PrettyForm>;
  matrix: ((m: MatrixLike, printer: PrettyPrinter) => PrettyForm) | undefined;
} = { extension: new Map(), matrix: undefined };

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** A one-character object of the current symbology (SymPy `xobj(symb, 1)`). */
function xchar(symb: string): string {
  return hobj(symb, 1);
}

const isExp = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
const isRat = (e: Expr, p: bigint, q = 1n): boolean => e instanceof Rational && e.p === p && e.q === q;
const isInfinity = (e: Expr): boolean => e instanceof Special && (e.name === 'oo' || e.name === '-oo');
const byKey = (a: Expr, b: Expr): number => compareKeys(sortKey(a), sortKey(b));

const ONE_KEY: Key = [[1, 0, 'Number'], [0, []], [], 1];

/**
 * SymPy default_sort_key of a dict key (an expression, number, boolean,
 * string, tuple or list), or undefined for a key Python could not hash.
 */
function dictKeySortKey(k: Printable): Key | undefined {
  if (k instanceof Expr) return sortKey(k);
  if (typeof k === 'number' || typeof k === 'bigint') return sortKey(impl.sympify(k));
  if (typeof k === 'boolean') return sortKey(k ? S.true : S.false);
  if (typeof k === 'string') return [[0, 0, 'str'], [1, [k]], ONE_KEY, 1];
  if (k instanceof PrettyTuple || Array.isArray(k)) {
    const items: readonly Printable[] = k instanceof PrettyTuple ? k.items : k;
    const keys = items.map(dictKeySortKey);
    const defined = keys.filter((x): x is Key => x !== undefined);
    if (defined.length !== keys.length) return undefined;
    return [[10, 0, k instanceof PrettyTuple ? 'tuple' : 'list'], [defined.length, defined], ONE_KEY, 1];
  }
  return undefined;
}

/** SymPy `is_Boolean` (boolean functions and atoms; not relations or symbols). */
function isBooleanNode(e: Expr): boolean {
  if (e instanceof BoolOp || e instanceof BoolAtom) return true;
  return e instanceof ExtensionExpr && ['Nand', 'Nor', 'Xnor', 'ITE', 'Implies', 'Equivalent'].includes(e.name);
}
const isNotNode = (e: Expr): boolean => e instanceof BoolOp && e.className === 'Not';

/** The members of hyper and meijerg the printer uses (functions/ is a higher layer). */
interface HyperLike {
  readonly argument: Expr;
  readonly ap: readonly Expr[];
  readonly bq: readonly Expr[];
}
interface MeijerLike {
  readonly argument: Expr;
  readonly an: readonly Expr[];
  readonly aother: readonly Expr[];
  readonly bm: readonly Expr[];
  readonly bother: readonly Expr[];
}
interface PermutationLike {
  readonly cyclicForm: readonly (readonly number[])[];
}
const isPermutationLike = (e: ExtensionExpr): e is ExtensionExpr & PermutationLike => e.name === 'Permutation' && 'cyclicForm' in e;
const isHyperLike = (e: ExtensionExpr): e is ExtensionExpr & HyperLike => e.name === 'hyper' && 'ap' in e && 'bq' in e;
const isMeijerLike = (e: ExtensionExpr): e is ExtensionExpr & MeijerLike => e.name === 'meijerg' && 'an' in e && 'bother' in e;

function isMatrixLike(x: unknown): x is MatrixLike {
  if (typeof x !== 'object' || x === null) return false;
  const m = x as { rows?: unknown; cols?: unknown; get?: unknown };
  return typeof m.rows === 'number' && typeof m.cols === 'number' && typeof m.get === 'function';
}

/** SymPy `requires_partial`: more than one non-integer free symbol. */
function requiresPartial(e: Expr): boolean {
  let n = 0;
  for (const s of impl.freeSymbols(e)) if (s.assumptions.integer !== true) n++;
  return n > 1;
}

/** Function names printed with a special name: [unicode, ascii]. */
const RENAMED: Readonly<Record<string, readonly [string, string]>> = {
  gamma: ['Γ', 'Gamma'],
  uppergamma: ['Γ', 'Gamma'],
  lowergamma: ['γ', 'lowergamma'],
  beta: ['Β', 'B'],
  fresnels: ['S', 'S'],
  fresnelc: ['C', 'C'],
  airyai: ['Ai', 'Ai'],
  airybi: ['Bi', 'Bi'],
  airyaiprime: ["Ai'", "Ai'"],
  airybiprime: ["Bi'", "Bi'"],
  LambertW: ['W', 'W'],
  lerchphi: ['Φ', 'lerchphi'],
  dirichlet_eta: ['η', 'dirichlet_eta'],
  mathieuc: ['C', 'C'],
  mathieus: ['S', 'S'],
  mathieucprime: ["C'", "C'"],
  mathieusprime: ["S'", "S'"],
  betainc: ["B'", "B'"],
  betainc_regularized: ['I', 'I'],
};

/** Number functions printed as a letter with the argument as subscript (SymPy `_print_number_function`). */
const NUMBER_FUNCTIONS: Readonly<Record<string, string>> = {
  euler: 'E',
  catalan: 'C',
  bernoulli: 'B',
  bell: 'B',
  lucas: 'L',
  fibonacci: 'F',
  tribonacci: 'T',
};

const NAMED_SETS: Readonly<Record<string, string>> = {
  EmptySet: 'EmptySet',
  Naturals: 'Naturals',
  Naturals0: 'Naturals0',
  Integers: 'Integers',
  Rationals: 'Rationals',
  Complexes: 'Complexes',
};

type Parenthesize = (x: Printable) => boolean;
const never: Parenthesize = () => false;

// ---------------------------------------------------------------------------
// The printer
// ---------------------------------------------------------------------------

/** SymPy `PrettyPrinter`: converts an expression into a 2D picture ({@link PrettyForm}). */
export class PrettyPrinter {
  readonly settings: Required<Omit<PrettyOptions, 'mulSymbol'>> & { readonly mulSymbol: string | undefined };
  /** SymPy `_print_level`: the nesting depth of the current `print` call. */
  private level = 0;

  constructor(options: PrettyOptions = {}) {
    const iu: string = options.imaginaryUnit ?? 'i';
    if (iu !== 'i' && iu !== 'j') throw new RangeError(`'imaginaryUnit' must be either 'i' or 'j', not '${String(iu)}'`);
    this.settings = {
      useUnicode: options.useUnicode ?? true,
      wrapLine: options.wrapLine ?? true,
      numColumns: options.numColumns ?? 80,
      orderTerms: options.orderTerms ?? 'lex',
      fullPrec: options.fullPrec ?? 'auto',
      mulSymbol: options.mulSymbol,
      imaginaryUnit: iu,
      rootNotation: options.rootNotation ?? true,
      useUnicodeSqrtChar: options.useUnicodeSqrtChar ?? true,
      matSymbolStyle: options.matSymbolStyle ?? 'plain',
    };
  }

  /** Whether unicode output is used. */
  get useUnicode(): boolean {
    return prettyUseUnicode();
  }

  /** SymPy `doprint`: the rendered string (lines wrapped per the settings). */
  doprint(e: Printable): string {
    return this.print(e).render({ wrapLine: this.settings.wrapLine, numColumns: this.settings.numColumns, useUnicode: this.settings.useUnicode });
  }

  /** SymPy `_print`: the picture of an expression or value. */
  print(e: Printable): PrettyForm {
    this.level++;
    try {
      return this.dispatch(e);
    } finally {
      this.level--;
    }
  }

  /** SymPy `emptyPrinter`: the str form on one line. */
  emptyPrinter(e: Expr): PrettyForm {
    return new PrettyForm(str(e));
  }

  private dispatch(e: Printable): PrettyForm {
    if (e instanceof PrettyForm) return e;
    if (e instanceof StringPict) return PrettyForm.of([e.picture.join('\n'), e.baseline]);
    if (typeof e === 'string') return new PrettyForm(e);
    if (typeof e === 'number' || typeof e === 'bigint') return this.print(impl.sympify(e));
    if (typeof e === 'boolean') return new PrettyForm(e ? 'True' : 'False');
    if (e instanceof PrettyTuple) return this.printTuple(e.items);
    if (Array.isArray(e)) return this.printSeq(e as readonly Printable[], '[', ']');
    if (e instanceof Map) return this.printDict(e as ReadonlyMap<Printable, Printable>);
    if (isMatrixLike(e)) return this.printMatrix(e);
    if (e instanceof Expr) return this.printExpr(e);
    throw new TypeError('pretty: cannot print this value');
  }

  private printExpr(e: Expr): PrettyForm {
    if (e instanceof Rational) return this.printRational(e);
    if (e instanceof Float) {
      const fp = this.settings.fullPrec;
      const full = fp === 'auto' ? this.level === 1 : fp;
      return new PrettyForm(floatString(e, !full));
    }
    if (e instanceof Sym) return new PrettyForm(prettySymbol(e.name));
    if (e instanceof Constant) return this.printConstant(e);
    if (e instanceof Special) return this.printSpecial(e);
    if (e instanceof BoolAtom) return new PrettyForm(e.value ? 'True' : 'False');
    if (e instanceof Add) return this.printAdd(e);
    if (e instanceof Mul) return this.printMul(e);
    if (e instanceof Pow) return this.printPow(e);
    if (e instanceof Fn) return this.printFn(e);
    if (e instanceof UndefFn) return this.printFunction(e.name, e.args);
    if (e instanceof Rel) return this.printRelational(e);
    if (e instanceof BoolOp) return this.printBoolOp(e);
    if (e instanceof Piecewise) return this.printPiecewise(e);
    if (e instanceof Integral) return this.printIntegral(e);
    if (e instanceof Derivative) return this.printDerivative(e);
    if (e instanceof Limit) return this.printLimit(e);
    if (e instanceof Order) return this.printOrder(e);
    if (e instanceof Concrete) return e.kind2 === 'Sum' ? this.printSum(e) : this.printProduct(e);
    const sc = setClass(e);
    if (sc !== undefined) return this.printSet(e, sc);
    if (e instanceof ExtensionExpr) return this.printExtension(e);
    return this.emptyPrinter(e);
  }

  // ---- atoms --------------------------------------------------------------

  private printConstant(e: Constant): PrettyForm {
    switch (e.name) {
      case 'E':
        return new PrettyForm(defined(prettyAtom('Exp1', 'e')));
      case 'pi':
        return new PrettyForm(prettyAtom('Pi') ?? 'pi');
      case 'I':
        return new PrettyForm(prettyAtom('ImaginaryUnit', undefined, this.settings.imaginaryUnit) ?? 'I');
      case 'EulerGamma':
        return new PrettyForm(this.useUnicode ? prettySymbol('gamma') : 'EulerGamma');
      case 'GoldenRatio':
        return new PrettyForm(this.useUnicode ? prettySymbol('phi') : 'GoldenRatio');
      case 'Catalan':
        return new PrettyForm(prettySymbol('G'));
      case 'TribonacciConstant':
        return new PrettyForm('TribonacciConstant');
    }
  }

  private printSpecial(e: Special): PrettyForm {
    switch (e.name) {
      case 'oo':
        return new PrettyForm(prettyAtom('Infinity') ?? 'oo');
      case '-oo':
        return new PrettyForm(prettyAtom('NegativeInfinity') ?? '-oo');
      case 'zoo':
      case 'nan':
        return new PrettyForm(e.name);
    }
  }

  private printRational(e: Rational): PrettyForm {
    const { p, q } = e;
    if (q === 1n) return p < 0n ? new PrettyForm(`${p}`, 0, Binding.NEG) : new PrettyForm(`${p}`);
    const abs = (x: bigint) => (x < 0n ? -x : x);
    if (abs(p) >= 10n && abs(q) >= 10n) {
      const num = p < 0n ? new PrettyForm(`${p}`, 0, Binding.NEG) : new PrettyForm(`${p}`);
      return num.div(new PrettyForm(`${q}`));
    }
    return this.emptyPrinter(e);
  }

  // ---- sequences ----------------------------------------------------------

  /** SymPy `_print_seq`: items separated by a delimiter, in optional brackets. */
  printSeq(
    seq: readonly Printable[],
    left?: string,
    right?: string,
    delimiter = ', ',
    parenthesize: Parenthesize = never,
    ifasciiNougly = true,
  ): PrettyForm {
    const pforms: PictLike[] = [];
    for (const item of seq) {
      let pform = this.print(item);
      if (parenthesize(item)) pform = PrettyForm.of(pform.parens());
      if (pforms.length > 0) pforms.push(delimiter);
      pforms.push(pform);
    }
    const s = pforms.length === 0 ? new StringPict('') : PrettyForm.of(StringPict.next(...pforms));
    return PrettyForm.of(s.parens(left ?? '', right ?? '', ifasciiNougly));
  }

  private printTuple(items: readonly Printable[]): PrettyForm {
    if (items.length === 1) {
      const pt = PrettyForm.of(StringPict.next(this.print(at(items, 0)), ','));
      return PrettyForm.of(pt.parens('(', ')', true));
    }
    return this.printSeq(items, '(', ')');
  }

  private printDict(d: ReadonlyMap<Printable, Printable>): PrettyForm {
    let entries = [...d.entries()];
    // SymPy sorts the keys by default_sort_key (keys that are not numbers, strings or expressions keep their order)
    const keys = entries.map(([k]) => dictKeySortKey(k));
    const sortable = keys.filter((k): k is Key => k !== undefined);
    if (sortable.length === keys.length) {
      entries = sortable
        .map((k, i) => [k, i] as const)
        .sort((p, q) => compareKeys(p[0], q[0]))
        .map(([, i]) => at(entries, i));
    }
    const items = entries.map(([k, v]) => PrettyForm.of(StringPict.next(this.print(k), ': ', this.print(v))));
    return this.printSeq(items, '{', '}');
  }

  // ---- functions ----------------------------------------------------------

  /** SymPy `_helper_print_function`: name(args) with the arguments in (big) parentheses. */
  printFunction(funcName: string, args0: readonly Expr[], opts: { sort?: boolean; left?: string; right?: string; delimiter?: string } = {}): PrettyForm {
    const args = opts.sort === true ? [...args0].sort(byKey) : args0;
    const prettyFunc = new PrettyForm(prettySymbol(funcName));
    const prettyArgs = PrettyForm.of(this.printSeq(args, undefined, undefined, opts.delimiter ?? ', ').parens(opts.left ?? '(', opts.right ?? ')'));
    const pform = PrettyForm.of(StringPict.next(prettyFunc, prettyArgs), Binding.FUNC);
    pform.prettyFunc = prettyFunc;
    pform.prettyArgs = prettyArgs;
    return pform;
  }

  private printFn(e: Fn): PrettyForm {
    const u = this.useUnicode;
    const a0 = at(e.args, 0);
    switch (e.name) {
      case 'abs':
        return PrettyForm.of(this.print(a0).parens('|', '|'));
      case 'conjugate': {
        const pform = this.print(a0);
        return PrettyForm.of(pform.above(hobj('_', pform.width())));
      }
      case 'floor':
      case 'ceiling':
        if (u) {
          const [l, r] = e.name === 'floor' ? ['lfloor', 'rfloor'] : ['lceil', 'rceil'];
          return PrettyForm.of(this.print(a0).parens(l, r));
        }
        return this.printFunction(e.name, e.args);
      case 'factorial':
      case 'factorial2':
      case 'subfactorial': {
        let pform = this.print(a0);
        const simple = (a0 instanceof Rational && a0.q === 1n && a0.p >= 0n) || a0 instanceof Sym;
        if (!simple) pform = PrettyForm.of(pform.parens());
        if (e.name === 'subfactorial') return PrettyForm.of(pform.left('!'));
        return PrettyForm.of(pform.right(e.name === 'factorial' ? '!' : '!!'));
      }
      case 'binomial': {
        const n = this.print(a0);
        const k = this.print(at(e.args, 1));
        const bar = ' '.repeat(Math.max(n.width(), k.width()));
        let pform = PrettyForm.of(k.above(bar));
        pform = PrettyForm.of(pform.above(n));
        pform = PrettyForm.of(pform.parens('(', ')'));
        pform.baseline = Math.floor((pform.baseline + 1) / 2);
        return pform;
      }
      case 'exp_polar':
        return new PrettyForm(defined(prettyAtom('Exp1', 'e'))).pow(this.print(a0));
      case 'atan2': {
        const pform = PrettyForm.of(this.printSeq(e.args).parens());
        return PrettyForm.of(pform.left('atan2'));
      }
      case 'KroneckerDelta': {
        let pform = this.print(a0);
        pform = PrettyForm.of(pform.right(new PrettyForm(',')));
        pform = PrettyForm.of(pform.right(this.print(at(e.args, 1))));
        const a = new StringPict(u ? prettySymbol('delta') : 'd');
        const top = new StringPict(...pform.left(' '.repeat(a.width())));
        const bot = new StringPict(...a.right(' '.repeat(pform.width())));
        return PrettyForm.of(bot.below(top), Binding.POW);
      }
      case 'primenu':
      case 'primeomega': {
        const pform = PrettyForm.of(this.print(a0).parens());
        const name = e.name === 'primenu' ? (u ? getOrThrow(greekUnicode, 'nu') : 'nu') : u ? getOrThrow(greekUnicode, 'Omega') : 'Omega';
        return PrettyForm.of(pform.left(name));
      }
      case 'expint': {
        const subscript = this.print(a0);
        // SymPy iterates the lines of the picture: each must be a known subscript
        if (u && subscript.picture.every((l) => sub.has(l))) {
          return this.printFunction(`E_${subscript.toString()}`, [at(e.args, 1)]);
        }
        return this.printFunction(e.name, e.args);
      }
      case 'Chi': {
        const prettyFunc = new PrettyForm('Chi');
        const prettyArgs = PrettyForm.of(this.printSeq(e.args).parens());
        const pform = PrettyForm.of(StringPict.next(prettyFunc, prettyArgs), Binding.FUNC);
        pform.prettyFunc = prettyFunc;
        pform.prettyArgs = prettyArgs;
        return pform;
      }
      default: {
        const named = this.printNamedFunction(e.name, e.args);
        if (named !== undefined) return named;
        const nf = NUMBER_FUNCTIONS[e.name];
        if (nf !== undefined) return this.printNumberFunction(e.args, nf);
        // (printNamedFunction already printed the RENAMED functions)
        return this.printFunction(sympyFunctionName(e.name), e.args);
      }
    }
  }

  /**
   * Functions whose node may be a core function or an extension node
   * (Heaviside, DiracDelta, elliptic integrals, polylog, stieltjes); undefined
   * for other names.
   */
  private printNamedFunction(name0: string, args: readonly Expr[]): PrettyForm | undefined {
    const u = this.useUnicode;
    switch (name0) {
      case 'SingularityFunction': {
        // SymPy _print_SingularityFunction: <x - a> raised to the exponent
        const shift = this.print(impl.add(at(args, 0), impl.mul(-1, at(args, 1))));
        const n = this.print(at(args, 2));
        const base = u ? PrettyForm.of(PrettyForm.of(new PrettyForm('<').right(shift)).right('>')) : this.printSeq([shift], '<', '>', ' ');
        return base.pow(n);
      }
      case 'Heaviside': {
        const name = u ? getOrThrow(greekUnicode, 'theta') : 'Heaviside';
        if (args.length === 1 || isRat(at(args, 1), 1n, 2n)) {
          const pform = PrettyForm.of(this.print(at(args, 0)).parens());
          return PrettyForm.of(pform.left(name));
        }
        return this.printFunction(name, args);
      }
      case 'DiracDelta': {
        if (!u) return this.printFunction('DiracDelta', args);
        const delta = getOrThrow(greekUnicode, 'delta');
        if (args.length === 2) {
          const a = new PrettyForm(delta);
          const b = PrettyForm.of(this.print(at(args, 1)).parens());
          const c = PrettyForm.of(this.print(at(args, 0)).parens());
          let pform = a.pow(b);
          pform = PrettyForm.of(pform.right(' '));
          return PrettyForm.of(pform.right(c));
        }
        const pform = PrettyForm.of(this.print(at(args, 0)).parens());
        return PrettyForm.of(pform.left(delta));
      }
      case 'stieltjes':
        return this.printNumberFunction(args, u ? getOrThrow(greekUnicode, 'gamma') : 'stieltjes');
      case 'polylog': {
        const subscript = this.print(at(args, 0));
        if (u && subscript.picture.every((l) => sub.has(l))) return this.printFunction(`Li_${subscript.toString()}`, [at(args, 1)]);
        return this.printFunction(name0, args);
      }
      case 'elliptic_k':
        return PrettyForm.of(PrettyForm.of(this.print(at(args, 0)).parens()).left('K'));
      case 'elliptic_f':
      case 'elliptic_e': {
        const p0 = this.print(at(args, 0));
        const pform = args.length === 1 ? p0 : this.hprintVseparator(p0, this.print(at(args, 1)), '', '', '', false);
        return PrettyForm.of(PrettyForm.of(pform.parens()).left(name0 === 'elliptic_f' ? 'F' : 'E'));
      }
      case 'elliptic_pi': {
        const name = u ? getOrThrow(greekUnicode, 'Pi') : 'Pi';
        const p0 = this.print(at(args, 0));
        const p1 = this.print(at(args, 1));
        let pform: PrettyForm;
        if (args.length === 2) pform = this.hprintVseparator(p0, p1, '', '', '', false);
        else {
          let pa = this.hprintVseparator(p1, this.print(at(args, 2)), '', '', '', false);
          pa = PrettyForm.of(pa.left('; '));
          pform = PrettyForm.of(pa.left(p0));
        }
        return PrettyForm.of(PrettyForm.of(pform.parens()).left(name));
      }
      default: {
        const renamed = RENAMED[name0];
        return renamed === undefined ? undefined : this.printFunction(u ? renamed[0] : renamed[1], args);
      }
    }
  }

  /** SymPy `_print_number_function`: name with the first argument as a subscript. */
  private printNumberFunction(args: readonly Expr[], name: string): PrettyForm {
    let pform = new PrettyForm(name);
    const arg = this.print(at(args, 0));
    let pformArg = new PrettyForm(' '.repeat(arg.width()));
    pformArg = PrettyForm.of(pformArg.below(arg));
    pform = PrettyForm.of(pform.right(pformArg));
    if (args.length === 1) return pform;
    const prettyFunc = pform;
    const prettyArgs = PrettyForm.of(this.printSeq([at(args, 1)]).parens());
    const out = PrettyForm.of(StringPict.next(prettyFunc, prettyArgs), Binding.FUNC);
    out.prettyFunc = prettyFunc;
    out.prettyArgs = prettyArgs;
    return out;
  }

  // ---- arithmetic ---------------------------------------------------------

  private orderedTerms(e: Add): Expr[] {
    return this.settings.orderTerms === 'none' ? [...e.args] : asOrderedTerms(e);
  }

  private printAdd(e: Add): PrettyForm {
    const terms = this.orderedTerms(e);
    const pforms: (PrettyForm | undefined)[] = [];
    const indices: [number, Rational][] = [];

    const prettyNegative = (pform: PrettyForm, index: number): PrettyForm => {
      const neg = index === 0 ? (pform.height() > 1 ? '- ' : '-') : ' - ';
      const p: StringPict = pform.binding > Binding.NEG || pform.binding === Binding.ADD ? new StringPict(...pform.parens()) : pform;
      return PrettyForm.of(StringPict.next(neg, p), Binding.NEG);
    };

    terms.forEach((term, i) => {
      if (term instanceof Mul && couldExtractMinusSign(term)) {
        // the negative number in front (couldExtractMinusSign)
        const coeff = splitCoeff(term)[0];
        const other = term.args.slice(1);
        const negArgs = isRat(coeff, -1n) ? other : [numNeg(coeff), ...other];
        pforms.push(prettyNegative(this.printMulArgs(negArgs), i));
      } else if (term instanceof Rational && term.q > 1n) {
        pforms.push(undefined);
        indices.push([i, term]);
      } else if ((isNum(term) && term.isNegative) || (term instanceof Special && term.name === '-oo')) {
        pforms.push(prettyNegative(this.print(isNum(term) ? numNeg(term) : impl.mul(-1, term)), i));
      } else if (term instanceof Rel) {
        pforms.push(PrettyForm.of(this.print(term).parens()));
      } else {
        pforms.push(this.print(term));
      }
    });

    if (indices.length > 0) {
      const large = pforms.some((p) => p !== undefined && p.height() > 1);
      for (const [i, t0] of indices) {
        let term = t0;
        let negative = false;
        if (term.p < 0n) {
          term = Rational.of(-term.p, term.q);
          negative = true;
        }
        let pform = large ? new PrettyForm(`${term.p}`).div(new PrettyForm(`${term.q}`)) : this.print(term);
        if (negative) pform = prettyNegative(pform, i);
        pforms[i] = pform;
      }
    }
    return PrettyForm.add(...pforms.map((p) => defined(p)));
  }

  /** SymPy `_print_Mul` of the given factors (an unevaluated Mul when built by the printer). */
  private printMulArgs(args: readonly Expr[]): PrettyForm {
    // Mul(*args, evaluate=False): with one argument it prints its only factor
    return this.printMulNode(new Mul(args), args);
  }

  private printMul(e: Mul): PrettyForm {
    return this.printMulNode(e, e.args);
  }

  private printMulNode(product: Mul, args: readonly Expr[]): PrettyForm {
    // an unevaluated Mul: identities and number factors are shown as given
    if (isRat(at(args, 0), 1n) || args.slice(1).some(isNum)) {
      const strargs = args.map((a) => this.print(a));
      const negone = at(strargs, 0).equals('-1');
      if (negone) strargs[0] = new PrettyForm('1', 0, 0);
      const obj = PrettyForm.mul(at(strargs, 0), ...strargs.slice(1));
      if (negone) return new PrettyForm(`-${obj.s}`, obj.baseline, obj.binding);
      return obj;
    }
    const factors = this.settings.orderTerms === 'none' || args.length < 2 ? [...args] : asOrderedFactors(product);
    const a: Expr[] = [];
    const b: Expr[] = [];
    for (const item of factors) {
      if (item instanceof Pow && item.isCommutative && !isExp(item) && item.exp instanceof Rational && item.exp.isNegative) {
        b.push(isRat(item.exp, -1n) ? item.base : new Pow(item.base, numNeg(item.exp)));
      } else if (item instanceof Rational) {
        if (item.p !== 1n) a.push(Rational.of(item.p));
        if (item.q !== 1n) b.push(Rational.of(item.q));
      } else {
        a.push(item);
      }
    }
    const pa = a.map((x) => this.print(x));
    const pb = b.map((x) => this.print(x));
    if (pb.length === 0) return PrettyForm.mul(at(pa, 0), ...pa.slice(1));
    if (pa.length === 0) pa.push(this.print(Rational.of(1n)));
    return PrettyForm.mul(at(pa, 0), ...pa.slice(1)).div(PrettyForm.mul(at(pb, 0), ...pb.slice(1)));
  }

  /** SymPy `_print_nth_root`: a radical sign over the base, with the index for roots other than 2. */
  private printNthRoot(base: Expr, root: Expr): PrettyForm {
    const bpretty = this.print(base);
    if (
      this.settings.useUnicodeSqrtChar &&
      this.useUnicode &&
      isRat(root, 2n) &&
      bpretty.height() === 1 &&
      (bpretty.width() === 1 || (base instanceof Rational && base.q === 1n && base.p >= 0n))
    ) {
      return PrettyForm.of(bpretty.left(getOrThrow(nthRoot, 2)));
    }
    const zZ = xchar('/');
    let rootsign = (xchar('\\')) + zZ;
    // the index is an integer or a symbol, printed on one line
    const rpretty = this.print(root);
    const exp = isRat(root, 2n) ? '' : rpretty.toString().padEnd(2);
    const expLen = Array.from(exp).length;
    if (expLen > 2) rootsign = ' '.repeat(expLen - 2) + rootsign;
    const rs = new StringPict(`${exp}\n${rootsign}`);
    rs.baseline = 0;
    const linelength = bpretty.height() - 1;
    const diag: string[] = [];
    for (let i = 0; i < linelength; i++) diag.push(' '.repeat(linelength - i - 1) + zZ + ' '.repeat(i));
    const diagonal = new StringPict(diag.join('\n'));
    diagonal.baseline = linelength - 1;
    const rootForm = PrettyForm.of(rs.right(diagonal));
    rootForm.baseline = Math.max(1, bpretty.baseline);
    let s = new PrettyForm(hobj('_', 2 + bpretty.width()));
    s = PrettyForm.of(bpretty.above(s));
    return PrettyForm.of(s.left(rootForm));
  }

  private printPow(power: Pow): PrettyForm {
    if (isExp(power)) return new PrettyForm(defined(prettyAtom('Exp1', 'e'))).pow(this.print(power.exp));
    let [b, e] = power.args;
    // SymPy as_base_exp: (1/q)**e is q**(-e)
    if (b instanceof Rational && b.p === 1n && b.q !== 1n) {
      e = impl.mul(-1, e);
      b = Rational.of(b.q);
    }
    if (power.isCommutative) {
      if (isRat(e, -1n)) return new PrettyForm('1').div(this.print(b));
      if (this.settings.rootNotation) {
        if (e instanceof Rational && e.p === 1n && e.q !== 1n) return this.printNthRoot(b, Rational.of(e.q));
        if (e instanceof Pow && e.base instanceof Sym && isRat(e.exp, -1n)) return this.printNthRoot(b, e.base);
      }
      if (e instanceof Rational && e.isNegative) return new PrettyForm('1').div(this.print(new Pow(b, numNeg(e))));
    }
    if (b instanceof Rel) return PrettyForm.of(this.print(b).parens()).pow(this.print(e));
    return this.print(b).pow(this.print(e));
  }

  // ---- relations and logic ------------------------------------------------

  private printRelational(e: Rel): PrettyForm {
    const ops = { Eq: '==', Ne: '!=', Lt: '<', Le: '<=', Gt: '>', Ge: '>=' } as const;
    const op = new PrettyForm(` ${xsym(ops[e.op])} `);
    return PrettyForm.of(StringPict.next(this.print(e.lhs), op, this.print(e.rhs)), Binding.OPEN);
  }

  private printBoolean(args0: readonly Expr[], ch: string, sort = true): PrettyForm {
    const args = sort ? [...args0].sort(byKey) : args0;
    const paren = (a: Expr): PrettyForm => {
      const p = this.print(a);
      return isBooleanNode(a) && !isNotNode(a) ? PrettyForm.of(p.parens()) : p;
    };
    let pform = paren(at(args, 0));
    for (const a of args.slice(1)) {
      pform = PrettyForm.of(pform.right(` ${ch} `));
      pform = PrettyForm.of(pform.right(paren(a)));
    }
    return pform;
  }

  private printBoolOp(e: BoolOp): PrettyForm {
    const name = e.className;
    return this.printBooleanByName(name, e.args);
  }

  private printBooleanByName(name: string, args: readonly Expr[], altchar?: string): PrettyForm {
    const u = this.useUnicode;
    switch (name) {
      case 'Not': {
        if (!u) return this.printFunction('Not', args);
        const arg = at(args, 0);
        if (arg instanceof BoolOp && (arg.className === 'Equivalent' || arg.className === 'Implies')) {
          return this.printBooleanByName(arg.className, arg.args, prettyAtom(arg.className === 'Equivalent' ? 'NotEquiv' : 'NotArrow'));
        }
        let pform = this.print(arg);
        if (isBooleanNode(arg) && !isNotNode(arg)) pform = PrettyForm.of(pform.parens());
        return PrettyForm.of(pform.left(defined(prettyAtom('Not'))));
      }
      case 'And':
      case 'Or':
      case 'Xor':
      case 'Nand':
      case 'Nor':
      case 'Equivalent':
        if (!u) return this.printFunction(name, args, { sort: true });
        return this.printBoolean(args, altchar ?? defined(prettyAtom(name === 'Equivalent' ? 'Equiv' : name)));
      case 'Implies':
        if (!u) return this.printFunction(name, args);
        return this.printBoolean(args, altchar ?? defined(prettyAtom('Arrow')), false);
      default:
        // ITE, the remaining core BoolOp
        return this.printITE(args);
    }
  }

  /** SymPy `_print_ITE`: ITE(a, b, c) printed as Piecewise((b, a), (c, True)). */
  private printITE(args: readonly Expr[]): PrettyForm {
    return this.print(new Piecewise([at(args, 1), at(args, 0), at(args, 2), S.true]));
  }

  private printPiecewise(e: Piecewise): PrettyForm {
    const pairs = e.pairs;
    const P = pairs.map(([x, c]) => [
      this.print(x),
      c instanceof BoolAtom && c.value ? new PrettyForm('otherwise') : PrettyForm.of(new PrettyForm('for ').right(this.print(c))),
    ]);
    const maxw = [0, 1].map((j) => Math.max(...P.map((row) => at(row, j).width())));
    let D: PrettyForm | undefined;
    for (const cells of P) {
      let Drow: PrettyForm | undefined;
      cells.forEach((p0, j) => {
        const wdelta = at(maxw, j) - p0.width();
        const wleft = Math.floor(wdelta / 2);
        let p = PrettyForm.of(p0.right(' '.repeat(wdelta - wleft)));
        p = PrettyForm.of(p.left(' '.repeat(wleft)));
        if (Drow === undefined) Drow = p;
        else {
          Drow = PrettyForm.of(Drow.right('  '));
          Drow = PrettyForm.of(Drow.right(p));
        }
      });
      const row = defined(Drow);
      if (D === undefined) D = row;
      else {
        D = PrettyForm.of(D.below(' '));
        D = PrettyForm.of(D.below(row));
      }
    }
    const out = PrettyForm.of(defined(D).parens('{', ''));
    out.baseline = Math.floor(out.height() / 2);
    out.binding = Binding.OPEN;
    return out;
  }

  // ---- calculus -----------------------------------------------------------

  private printIntegral(e: Integral): PrettyForm {
    // nested integrals print as one multiple integral, innermost limits first
    const limits: Expr[][] = [];
    let cur: Expr = e;
    while (cur instanceof Integral) {
      limits.unshift(cur.args.slice(1));
      cur = cur.integrand;
    }
    const f = cur;
    let prettyF = this.print(f);
    if (f instanceof Add) prettyF = PrettyForm.of(prettyF.parens());
    let arg = prettyF;
    for (const x of limits) {
      let prettyArg = this.print(at(x, 0));
      if (prettyArg.width() > 1) prettyArg = PrettyForm.of(prettyArg.parens());
      arg = PrettyForm.of(arg.right(' d', prettyArg));
    }
    const ascii = !this.useUnicode;
    let s: PrettyForm | undefined;
    for (const lim of limits) {
      const h = arg.height();
      let H = h + 2;
      if (ascii) H += 2;
      let pform = new PrettyForm(vobj('int', H));
      pform.baseline = arg.baseline + Math.floor((H - h) / 2);
      if (lim.length > 1) {
        let prettyA = lim.length === 2 ? new PrettyForm('') : this.print(at(lim, 1));
        let prettyB = this.print(last(lim));
        if (ascii) {
          prettyB = PrettyForm.of(prettyB.left(' '.repeat(Math.max(1, 3 - prettyB.width()))));
          prettyA = PrettyForm.of(prettyA.right(' '.repeat(Math.max(1, 4 - prettyA.width()))));
        }
        pform = PrettyForm.of(pform.above(prettyB));
        pform = PrettyForm.of(pform.below(prettyA));
      }
      if (!ascii) pform = PrettyForm.of(pform.right(' '));
      s = s === undefined ? pform : PrettyForm.of(s.left(pform));
    }
    const out = PrettyForm.of(arg.left(defined(s)));
    out.binding = Binding.MUL;
    return out;
  }

  private sumProductLimits(lim: readonly Expr[]): [PrettyForm, PrettyForm] {
    const op = new PrettyForm(` ${xsym('==')} `);
    const lower = PrettyForm.of(StringPict.next(this.print(at(lim, 0)), op, this.print(at(lim, 1))));
    return [lower, this.print(at(lim, 2))];
  }

  private printProduct(e: Concrete): PrettyForm {
    let prettyFunc = this.print(e.function);
    let horizontal = xchar('_');
    let corner = xchar('_');
    const vertical = xchar('|');
    if (this.useUnicode) {
      horizontal = xchar('-');
      corner = xchar('UpTack');
    }
    const funcHeight = prettyFunc.height();
    let first = true;
    let maxUpper = 0;
    let signHeight = 0;
    for (const lim of e.limits) {
      const [prettyLower, prettyUpper] = this.sumProductLimits(lim);
      const width = Math.floor(((funcHeight + 2) * 5) / 3) - 2;
      const signLines = [horizontal + corner + horizontal.repeat(width - 2) + corner + horizontal];
      for (let i = 0; i < funcHeight + 1; i++) signLines.push(` ${vertical}${' '.repeat(width - 2)}${vertical} `);
      let prettySign = PrettyForm.of(StringPict.stack(...signLines));
      maxUpper = Math.max(maxUpper, prettyUpper.height());
      if (first) signHeight = prettySign.height();
      prettySign = PrettyForm.of(prettySign.above(prettyUpper));
      prettySign = PrettyForm.of(prettySign.below(prettyLower));
      if (first) {
        prettyFunc.baseline = 0;
        first = false;
      }
      const height = prettySign.height();
      const padding = PrettyForm.of(StringPict.stack(...Array<string>(height - 1).fill(' ')));
      prettySign = PrettyForm.of(prettySign.right(padding));
      prettyFunc = PrettyForm.of(prettySign.right(prettyFunc));
    }
    prettyFunc.baseline = maxUpper + Math.floor(signHeight / 2);
    prettyFunc.binding = Binding.MUL;
    return prettyFunc;
  }

  private printSum(e: Concrete): PrettyForm {
    const ascii = !this.useUnicode;
    const asum = (hrequired: number, useAscii: boolean): [number, number, string[], number] => {
      const h = Math.max(hrequired, 2);
      let d = Math.floor(h / 2);
      let w = d + 1;
      const more = hrequired % 2;
      const lines: string[] = [];
      if (useAscii) {
        lines.push(`${'_'.repeat(w)} `);
        lines.push(`\\${' '.repeat(w - 1)}\``);
        for (let i = 1; i < d; i++) lines.push(`${' '.repeat(i)}\\${' '.repeat(w - i)}`);
        if (more) lines.push(`${' '.repeat(d)})${' '.repeat(w - d)}`);
        for (let i = d - 1; i >= 1; i--) lines.push(`${' '.repeat(i)}/${' '.repeat(w - i)}`);
        lines.push(`/${'_'.repeat(w - 1)},`);
        return [d, h + more, lines, more];
      }
      w += more;
      d += more;
      const vsum = vobj('sum', 4);
      lines.push('_'.repeat(w));
      for (let i = 0; i < d; i++) lines.push(`${' '.repeat(i)}${at(vsum, 2)}${' '.repeat(w - i - 1)}`);
      for (let i = d - 1; i >= 0; i--) lines.push(`${' '.repeat(i)}${at(vsum, 4)}${' '.repeat(w - i - 1)}`);
      lines.push(at(vsum, 8).repeat(w));
      return [d, h + 2 * more, lines, more];
    };

    const f = e.function;
    let prettyF = this.print(f);
    if (f instanceof Add) prettyF = PrettyForm.of(prettyF.parens());
    const H = prettyF.height() + 2;
    let first = true;
    let maxUpper = 0;
    let signHeight = 0;
    let adjustment = 0;
    for (const lim of e.limits) {
      const [prettyLower, prettyUpper] = this.sumProductLimits(lim);
      maxUpper = Math.max(maxUpper, prettyUpper.height());
      const [d, h, slines, adj] = asum(H, ascii);
      adjustment = adj;
      let prettySign = PrettyForm.of(StringPict.stack(...slines));
      if (first) signHeight = prettySign.height();
      prettySign = PrettyForm.of(prettySign.above(prettyUpper));
      prettySign = PrettyForm.of(prettySign.below(prettyLower));
      if (first) {
        prettyF.baseline -= d - (Math.floor(prettyF.height() / 2) - prettyF.baseline);
        first = false;
      }
      const pad = PrettyForm.of(StringPict.stack(...Array<string>(h).fill(' ')));
      prettySign = PrettyForm.of(prettySign.right(pad));
      prettyF = PrettyForm.of(prettySign.right(prettyF));
    }
    const asciiAdjustment = adjustment === 0 ? (ascii ? 1 : 0) : 0;
    prettyF.baseline = maxUpper + Math.floor(signHeight / 2) + asciiAdjustment;
    prettyF.binding = Binding.MUL;
    return prettyF;
  }

  private printDerivative(deriv: Derivative): PrettyForm {
    const derivSymbol = requiresPartial(deriv.expr) && this.useUnicode ? '∂' : 'd';
    let x: PrettyForm | undefined;
    let countTotal = 0;
    for (const [sym, num] of [...deriv.variableCount].reverse()) {
      const s = this.print(sym);
      let ds = PrettyForm.of(s.left(derivSymbol));
      countTotal += num;
      if (num > 1) ds = ds.pow(new PrettyForm(`${num}`));
      if (x === undefined) x = ds;
      else {
        x = PrettyForm.of(x.right(' '));
        x = PrettyForm.of(x.right(ds));
      }
    }
    const f = PrettyForm.of(this.print(deriv.expr).parens(), Binding.FUNC);
    let pform = new PrettyForm(derivSymbol);
    if (countTotal > 1) pform = pform.pow(new PrettyForm(`${countTotal}`));
    pform = PrettyForm.of(pform.below(LINE, defined(x)));
    pform.baseline = pform.baseline + 1;
    pform = PrettyForm.of(StringPict.next(pform, f));
    pform.binding = Binding.MUL;
    return pform;
  }

  private printLimit(l: Limit): PrettyForm {
    const [e, z, z0] = [at(l.args, 0), at(l.args, 1), at(l.args, 2)];
    let E = this.print(e);
    if (precedence(e) <= PREC.MUL) E = PrettyForm.of(E.parens('(', ')'));
    let Lim = new PrettyForm('lim');
    let LimArg = this.print(z);
    if (this.useUnicode) LimArg = PrettyForm.of(LimArg.right(`${xchar('-')}${defined(prettyAtom('Arrow'))}`));
    else LimArg = PrettyForm.of(LimArg.right('->'));
    LimArg = PrettyForm.of(LimArg.right(this.print(z0)));
    let dir: string = l.dir;
    if (l.dir === '+-' || isInfinity(z0)) dir = '';
    else if (this.useUnicode) dir = defined(prettyAtom(l.dir === '+' ? 'SuperscriptPlus' : 'SuperscriptMinus'));
    LimArg = PrettyForm.of(LimArg.right(this.print(dir)));
    Lim = PrettyForm.of(Lim.below(LimArg));
    return PrettyForm.of(Lim.right(E), Binding.MUL);
  }

  private printOrder(e: Order): PrettyForm {
    let pform = this.print(e.expr);
    const nv = Math.max(0, e.args.length - 2);
    const variables = e.args.slice(1, 1 + nv);
    const point = e.args.length >= 3 ? last(e.args) : undefined;
    const nonzero = point !== undefined && !isRat(point, 0n);
    if (point !== undefined && ((nonzero && variables.length > 0) || variables.length > 1)) {
      pform = PrettyForm.of(pform.right('; '));
      if (variables.length > 1) pform = PrettyForm.of(pform.right(this.printTuple(variables)));
      else pform = PrettyForm.of(pform.right(this.print(at(variables, 0))));
      pform = PrettyForm.of(pform.right(this.useUnicode ? ` ${defined(prettyAtom('Arrow'))} ` : ' -> '));
      if (variables.length > 1) pform = PrettyForm.of(pform.right(this.printTuple(variables.map(() => point))));
      else pform = PrettyForm.of(pform.right(this.print(point)));
    }
    pform = PrettyForm.of(pform.parens());
    return PrettyForm.of(pform.left('O'));
  }

  // ---- sets ---------------------------------------------------------------

  private hprintVseparator(p1: Printable, p2: Printable, left: string, right: string, delimiter: string, ifasciiNougly: boolean): PrettyForm {
    if (ifasciiNougly && !this.useUnicode) return this.printSeq([p1, '|', p2], left, right, delimiter, never, true);
    const tmp = this.printSeq([p1, p2], left, right, delimiter);
    const sep = new StringPict(vobj('|', tmp.height()), tmp.baseline);
    return this.printSeq([p1, sep, p2], left, right, delimiter);
  }

  private printSet(e: Expr, cls: string): PrettyForm {
    const u = this.useUnicode;
    const isSet = (x: Printable, ...names: string[]): boolean => x instanceof Expr && names.some((n) => setClass(x) === n);
    switch (cls) {
      case 'Interval': {
        const [a, b, lo, ro] = [at(e.args, 0), at(e.args, 1), at(e.args, 2), at(e.args, 3)];
        if (a.key === b.key) return this.printSeq([a], '{', '}');
        const open = (x: Expr) => x instanceof BoolAtom && x.value;
        return this.printSeq([a, b], open(lo) ? '(' : '[', open(ro) ? ')' : ']');
      }
      case 'FiniteSet':
        return this.printSeq([...e.args].sort(byKey), '{', '}', ', ');
      case 'Range': {
        const shown = rangePrintForm(e, 4);
        // a Range whose elements are unknown (SymPy's pretty printer raises an error; the
        // function form of SymPy's LaTeX printer is shown)
        if ('symbolic' in shown) return this.printFunction('Range', shown.symbolic);
        return this.printSeq(shown.elements.map((t) => (t === DOTS ? (u ? defined(prettyAtom('Dots')) : '...') : t)), '{', '}', ', ');
      }
      case 'ProductSet': {
        // SymPy _print_ProductSet: a power when every factor is the same set
        const sets = e.args;
        if (sets.every((x) => x.key === at(sets, 0).key)) return this.print(at(sets, 0)).pow(this.print(impl.sympify(sets.length)));
        return this.printSeq(sets, undefined, undefined, ` ${u ? defined(prettyAtom('Multiplication')) : 'x'} `, (x) => isSet(x, 'Union', 'Intersection', 'ProductSet'));
      }
      case 'CartesianComplexRegion':
      case 'PolarComplexRegion': {
        // SymPy _print_ComplexRegion: {x + y*I | x, y in sets} or {r*(I*sin(theta) + cos(theta)) | r, theta in sets}
        const polar = cls === 'PolarComplexRegion';
        const [a, b] = polar ? [new Dummy('r'), new Dummy('theta')] : [new Dummy('x'), new Dummy('y')];
        const expr = polar ? impl.mul(a, impl.add(impl.mul(S.I, new Fn('sin', [b])), new Fn('cos', [b]))) : impl.add(a, impl.mul(b, S.I));
        const inn = u ? defined(prettyAtom('SmallElementOf')) : 'in';
        const C = this.printSeq([this.printSeq([a, b]), inn, this.print(at(e.args, 0))], undefined, undefined, ' ');
        return this.hprintVseparator(this.print(expr), C, '{', '}', ' ', true);
      }
      case 'Union':
        return this.printSeq(setArgsOrdered(e.args), undefined, undefined, ` ${defined(prettyAtom('Union', 'U'))} `, (s) => isSet(s, 'ProductSet', 'Intersection', 'Complement'));
      case 'Intersection':
        return this.printSeq(setArgsOrdered(e.args), undefined, undefined, ` ${defined(prettyAtom('Intersection', 'n'))} `, (s) => isSet(s, 'ProductSet', 'Union', 'Complement'));
      case 'Complement':
        return this.printSeq(e.args, undefined, undefined, ' \\ ', (s) => isSet(s, 'ProductSet', 'Intersection', 'Union'));
      case 'Reals':
        return u ? new PrettyForm(defined(prettyAtom('Reals'))) : this.printSeq(['-oo', 'oo'], '(', ')');
      case 'UniversalSet':
        return new PrettyForm(u ? defined(prettyAtom('Universe')) : 'UniversalSet');
      case 'ImageSet': {
        const [v, expr, base] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
        const inn = u ? defined(prettyAtom('SmallElementOf')) : 'in';
        const S = this.printSeq([v, inn, base], undefined, undefined, ' ');
        return this.hprintVseparator(this.print(expr), S, '{', '}', ' ', true);
      }
      case 'ConditionSet': {
        const [v, cond0, base] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
        const inn = u ? defined(prettyAtom('SmallElementOf')) : 'in';
        const and = u ? defined(prettyAtom('And')) : 'and';
        const variables = this.printSeq([v]);
        let cond = this.print(cond0);
        if (u) cond = PrettyForm.of(cond.parens());
        if (setClass(base) === 'UniversalSet') return this.hprintVseparator(variables, cond, '{', '}', ' ', true);
        const C = this.printSeq([variables, inn, this.print(base), and, cond], undefined, undefined, ' ');
        return this.hprintVseparator(variables, C, '{', '}', ' ', true);
      }
      default: {
        const named = NAMED_SETS[cls];
        if (named !== undefined) return new PrettyForm(prettyAtom(cls) ?? named);
        return this.emptyPrinter(e);
      }
    }
  }

  // ---- other nodes ----------------------------------------------------------

  private printMatrix(m: MatrixLike): PrettyForm {
    if (prettyHooks.matrix) return prettyHooks.matrix(m, this);
    const D = this.printMatrixContents(m);
    D.baseline = Math.floor(D.height() / 2);
    return PrettyForm.of(D.parens('[', ']'));
  }

  /** SymPy `_print_matrix_contents`: the grid of entries (without brackets). */
  printMatrixContents(m: MatrixLike): PrettyForm {
    const Ms: PrettyForm[][] = [];
    for (let i = 0; i < m.rows; i++) {
      const row: PrettyForm[] = [];
      for (let j = 0; j < m.cols; j++) row.push(this.print(m.get(i, j)));
      Ms.push(row);
    }
    const maxw: number[] = [];
    for (let j = 0; j < m.cols; j++) maxw.push(Math.max(0, ...Ms.map((r) => at(r, j).width())));
    let D: PrettyForm | undefined;
    for (let i = 0; i < m.rows; i++) {
      let Drow: PrettyForm | undefined;
      for (let j = 0; j < m.cols; j++) {
        let s = at(at(Ms, i), j);
        const [left, right] = centerPad(s.width(), at(maxw, j));
        s = PrettyForm.of(s.right(right));
        s = PrettyForm.of(s.left(left));
        if (Drow === undefined) {
          Drow = s;
          continue;
        }
        Drow = PrettyForm.of(Drow.right('  '));
        Drow = PrettyForm.of(Drow.right(s));
      }
      if (Drow === undefined) continue;
      if (D === undefined) {
        D = Drow;
        continue;
      }
      D = PrettyForm.of(D.below(' '));
      D = PrettyForm.of(D.below(Drow));
    }
    return D ?? new PrettyForm('');
  }

  /**
   * SymPy `_print_Permutation` with perm_cyclic=True (`_print_Cycle` of
   * Cycle(p)): the cycles without the singletons, () for an identity.
   */
  private printPermutation(e: PermutationLike): PrettyForm {
    if (e.cyclicForm.length === 0) return PrettyForm.of(new StringPict('').parens());
    return new PrettyForm(e.cyclicForm.map((c) => `(${c.join(' ')})`).join(''));
  }

  /** SymPy `_hprint_vec`. */
  private hprintVec(v: readonly Expr[]): PrettyForm {
    let D: PrettyForm | undefined;
    for (const a of v) D = D === undefined ? this.print(a) : PrettyForm.of(PrettyForm.of(D.right(', ')).right(this.print(a)));
    return D ?? new PrettyForm(' ');
  }

  /** The parameter table of hyper or meijerg next to |z, in parentheses (SymPy _print_hyper, _print_meijerg). */
  private parameterTable(D0: PrettyForm, z: Expr): PrettyForm {
    let D = D0;
    let P = this.print(z);
    P.baseline = Math.floor(P.height() / 2);
    D.baseline = Math.floor(D.height() / 2);
    P = PrettyForm.of(P.left(' '));
    D = PrettyForm.of(D.right(' '));
    D = this.hprintVseparator(D, P, '', '', '', false);
    return PrettyForm.of(D.parens('(', ')'));
  }

  /** The F or G of hyper or meijerg, as tall as the table D. */
  private annotatedLetter(letter: 'F' | 'G', D: PrettyForm): [PrettyForm, number, number, number] {
    const above = Math.floor(D.height() / 2) - 1;
    const below = D.height() - above - 1;
    const [sz, t, b, add, img] = annotated(letter);
    const F = new PrettyForm('\n'.repeat(Math.max(0, above - t)) + img + '\n'.repeat(Math.max(0, below - b)), above + sz);
    return [F, above, sz, add];
  }

  /** SymPy `_print_hyper`. */
  private printHyper(e: HyperLike): PrettyForm {
    let D = PrettyForm.of(PrettyForm.of(this.hprintVec(e.ap).below(' ')).below(this.hprintVec(e.bq)));
    D = this.parameterTable(D, e.argument);
    const [F0, above, sz] = this.annotatedLetter('F', D);
    let F = PrettyForm.of(F0.left(this.print(impl.sympify(e.ap.length))));
    F = PrettyForm.of(F.right(this.print(impl.sympify(e.bq.length))));
    F.baseline = above + Math.floor((sz + 1) / 2);
    return PrettyForm.of(F.right(' ', D));
  }

  /** SymPy `_print_meijerg`. */
  private printMeijer(e: MeijerLike): PrettyForm {
    const cells = [[e.an, e.aother].map((v) => this.hprintVec(v)), [e.bm, e.bother].map((v) => this.hprintVec(v))];
    for (let i = 0; i < 2; i++) {
      const maxw = Math.max(at(at(cells, 0), i).width(), at(at(cells, 1), i).width());
      for (let j = 0; j < 2; j++) {
        const s = at(at(cells, j), i);
        const left = Math.floor((maxw - s.width()) / 2);
        const right = maxw - left - s.width();
        at(cells, j)[i] = PrettyForm.of(PrettyForm.of(s.left(' '.repeat(left))).right(' '.repeat(right)));
      }
    }
    const row = (j: number) => PrettyForm.of(at(at(cells, j), 0).right('  ', at(at(cells, j), 1)));
    let D = PrettyForm.of(PrettyForm.of(row(0).below(' ')).below(row(1)));
    D = this.parameterTable(D, e.argument);
    const [F0, above, , add] = this.annotatedLetter('G', D);
    const adjust = (p1: PrettyForm, p2: PrettyForm): [PrettyForm, PrettyForm] => {
      const diff = p1.width() - p2.width();
      if (diff === 0) return [p1, p2];
      return diff > 0 ? [p1, PrettyForm.of(p2.left(' '.repeat(diff)))] : [PrettyForm.of(p1.left(' '.repeat(-diff))), p2];
    };
    const size = (v: readonly Expr[]) => this.print(impl.sympify(v.length));
    const [pp, pm] = adjust(size([...e.an, ...e.aother]), size(e.bm));
    const [pq, pn] = adjust(size([...e.bm, ...e.bother]), size(e.an));
    // SymPy pads the upper counts with F.baseline - above - 2 lines, one for the three lines of G
    const pu = PrettyForm.of(PrettyForm.of(pm.right(', ', pn)).below('\n'));
    const pl = PrettyForm.of(pp.right(', ', pq));
    const p = PrettyForm.of(pu.below(pl));
    F0.baseline = above;
    const F = PrettyForm.of(F0.right(p));
    F.baseline = above + add;
    return PrettyForm.of(F.right(' ', D));
  }

  private printExtension(e: ExtensionExpr): PrettyForm {
    const hook = prettyHooks.extension.get(e.name);
    if (hook) return hook(e, this);
    const named = this.printNamedFunction(e.name, e.args);
    if (named !== undefined) return named;
    const u = this.useUnicode;
    if (isSequence(e) && !hasSymbolicBounds(e)) {
      // SymPy _print_SeqFormula (and SeqPer, SeqAdd, SeqMul): the first terms as a list
      return this.printSeq(sequencePrintset(e).map((t) => (t === DOTS ? (u ? defined(prettyAtom('Dots')) : '...') : t)), '[', ']');
    }
    if (isPermutationLike(e)) return this.printPermutation(e);
    if (isHyperLike(e)) return this.printHyper(e);
    if (isMeijerLike(e)) return this.printMeijer(e);
    switch (e.name) {
      // SymPy Partition is a FiniteSet of its blocks (stored in SymPy's order): _print_FiniteSet
      case 'Partition':
        return this.printSeq(e.args, '{', '}', ', ');
      case 'Contains': {
        // SymPy _print_Contains: x ∈ S in unicode, the str form in ASCII
        if (!u) return this.emptyPrinter(e);
        return PrettyForm.of(StringPict.next(this.print(at(e.args, 0)), ` ${defined(prettyAtom('ElementOf'))} `, this.print(at(e.args, 1))), Binding.OPEN);
      }
      case 'Mod': {
        let pform = this.print(at(e.args, 0));
        if (pform.binding > Binding.MUL) pform = PrettyForm.of(pform.parens());
        pform = PrettyForm.of(pform.right(' mod '));
        pform = PrettyForm.of(pform.right(this.print(at(e.args, 1))));
        pform.binding = Binding.OPEN;
        return pform;
      }
      case 'AccumBounds':
        return this.printSeq(e.args.slice(0, 2), '<', '>');
      case 'Lambda': {
        const vars = e.args.slice(0, -1);
        const expr = last(e.args);
        const arrow = u ? ` ${defined(prettyAtom('ArrowFromBar'))} ` : ' -> ';
        const varForm = vars.length === 1 && vars[0] instanceof Sym ? this.print(vars[0]) : this.printTuple(vars);
        return PrettyForm.of(StringPict.next(varForm, arrow, this.print(expr)), Binding.LINE);
      }
      case 'Subs': {
        const n = (e.args.length - 1) / 2;
        const variables = e.args.slice(1, 1 + n);
        const point = e.args.slice(1 + n);
        let pform = PrettyForm.of(this.print(at(e.args, 0)).parens());
        const h = pform.height() > 1 ? pform.height() : 2;
        const rvert = new StringPict(vobj('|', h), pform.baseline);
        pform = PrettyForm.of(pform.right(rvert));
        const b = pform.baseline;
        pform.baseline = pform.height() - 1;
        const items = variables.map((v, i) => this.printSeq([this.print(v), xsym('=='), this.print(at(point, i))], undefined, undefined, ''));
        pform = PrettyForm.of(pform.right(this.printSeq(items)));
        pform.baseline = b;
        return pform;
      }
      case 'Nand':
      case 'Nor':
        return this.printBooleanByName(e.name, e.args);
      case 'ITE':
        return this.printITE(e.args);
      default: {
        // a function-like node (str form Name(args)) prints as a function; anything else as its str form
        const s = str(e);
        if (s === `${e.name}(${e.args.map(str).join(', ')})`) return this.printFunction(e.name, e.args);
        return new PrettyForm(s);
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

/**
 * SymPy `pretty(expr, **settings)`: a string containing the 2D pretty form
 * of `expr` (unicode by default).
 *
 * @example
 * ```ts
 * pretty(parse('x**2 + 2*x + 1'));
 * // ' 2          \nx  + 2⋅x + 1'
 * ```
 */
export function pretty(expr: Printable, options: PrettyOptions = {}): string {
  const pp = new PrettyPrinter(options);
  const prev = prettyUseUnicode(pp.settings.useUnicode);
  const prevMul = prettyMulSymbol(options.mulSymbol);
  try {
    return pp.doprint(expr);
  } finally {
    prettyUseUnicode(prev);
    prettyMulSymbol(prevMul);
  }
}

/**
 * SymPy `pretty_print(expr, **settings)` / `pprint`. SymPy prints the
 * pretty form; symjs has no console output, so this returns the text that
 * would be printed (the pretty form followed by a newline).
 */
export function prettyPrint(expr: Printable, options: PrettyOptions = {}): string {
  return `${pretty(expr, options)}\n`;
}

/** SymPy `pprint`: alias of {@link prettyPrint} (returns the text that would be printed). */
export const pprint: (expr: Printable, options?: PrettyOptions) => string = prettyPrint;

/**
 * SymPy `pager_print`: the pretty form meant for a pager. Lines are not
 * wrapped unless `numColumns` is given (SymPy uses 500000 columns). Returns
 * the text instead of opening a pager.
 */
export function pagerPrint(expr: Printable, options: PrettyOptions = {}): string {
  return pretty(expr, { ...options, numColumns: options.numColumns ?? 500000 });
}
