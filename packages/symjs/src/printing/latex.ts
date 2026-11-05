// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file LaTeX printer compatible with SymPy's `LatexPrinter` and its
 * settings (`latex(expr, { mode: 'inline', mulSymbol: 'dot', ... })`).
 */

import { isNegative } from '../core/assumptions';
import { Add, Expr, ExtensionExpr, BoolAtom, Constant, Derivative, Float, Fn, Integral, Limit, Mul, Order, Piecewise, Pow, Rational, Rel, S, Special, Sym, UndefFn, impl, isNum } from '../core/nodes';
import { mul, pow, splitCoeff, sympify } from '../core/ops';
import { numNeg } from '../core/num';
import { asOrderedFactors, asOrderedTerms, compareKeys, sortKey } from './sortkey';
import { PREC, declaredPrecedence, floatString, precedence as strPrecedence, startsNegative, str } from './str';
import { BoolOp } from '../core/boolalg';
import { Concrete } from '../core/concrete';
import { DOTS, rangePrintForm, setArgsOrdered, setClass } from './sets';
import { hasSymbolicBounds, isSequence, sequencePrintset } from './sequences';
import { at } from '../core/guard';

// ---------------------------------------------------------------------------
// Settings
// ---------------------------------------------------------------------------

/** Settings of the LaTeX printer (SymPy's `LatexPrinter` settings in camelCase). */
export interface LatexOptions {
  /** 'plain' (default), 'inline' (`$...$`), 'equation' or 'equation*' (a LaTeX environment). */
  readonly mode?: 'plain' | 'inline' | 'equation' | 'equation*';
  /** itex syntax: `$$...$$` for the equation modes, `\root{n}{x}`, `\gt` and `\lt`. */
  readonly itex?: boolean;
  /** Rational powers as `x^{p/q}` instead of `x^{\frac{p}{q}}`. */
  readonly foldFracPowers?: boolean;
  /** No brackets around a simple function argument (`\sin {x}`). */
  readonly foldFuncBrackets?: boolean;
  /** Short fractions as `p / q` (default: only in 'inline' mode). */
  readonly foldShortFrac?: boolean;
  /** Inverse trigonometric functions as `\operatorname{asin}` ('abbreviated', default), `\arcsin` ('full') or `\sin^{-1}` ('power'). */
  readonly invTrigStyle?: 'abbreviated' | 'full' | 'power';
  /** `\ln` instead of `\log` for the natural logarithm. */
  readonly lnNotation?: boolean;
  /** A fraction whose numerator has more than this ratio of terms to the denominator is split. */
  readonly longFracRatio?: number;
  /** The delimiter of matrices: '[' (default), '(' or '' for none. */
  readonly matDelim?: '[' | '(' | '';
  /** The matrix environment (default 'matrix', 'array' beyond 10 columns, 'smallmatrix' inline). */
  readonly matStr?: string;
  /** The multiplication symbol: none (a space, default), 'ldot', 'dot', 'times' or any LaTeX string. */
  readonly mulSymbol?: 'ldot' | 'dot' | 'times' | (string & Record<never, never>);
  /** The LaTeX of chosen symbols (SymPy `symbol_names`). */
  readonly symbolNames?: ReadonlyMap<Expr, string>;
  /** Roots as `\sqrt` (default true); false prints fractional powers. */
  readonly rootNotation?: boolean;
  /** The imaginary unit: 'i' (default), 'j', 'ri', 'rj', 'ti', 'tj' or any LaTeX string. */
  readonly imaginaryUnit?: string;
  /** `\Re` and `\Im` instead of `\operatorname{re}` and `\operatorname{im}`. */
  readonly gothicReIm?: boolean;
  /** The decimal separator of floats, 'period' (default) or 'comma' (then lists use ';'). */
  readonly decimalSeparator?: 'period' | 'comma';
  /** Superscripted bases raised to a power in parentheses (default true), else in braces. */
  readonly parenthesizeSuper?: boolean;
  /** The differential operator: 'd' (default), 'rd', 'td' or any LaTeX string. */
  readonly diffOperator?: string;
  /** Print symbol names as they are, without sub- and superscripts. */
  readonly disableSplitSuperSub?: boolean;
  /** Floats with all their digits (default false: trailing zeros dropped). */
  readonly fullPrec?: boolean;
}

interface Settings {
  readonly mode: 'plain' | 'inline' | 'equation' | 'equation*';
  readonly itex: boolean;
  readonly foldFracPowers: boolean;
  readonly foldFuncBrackets: boolean;
  readonly foldShortFrac: boolean;
  readonly invTrigStyle: 'abbreviated' | 'full' | 'power';
  readonly lnNotation: boolean;
  readonly longFracRatio: number | undefined;
  readonly matDelim: '[' | '(' | '';
  readonly matStr: string | undefined;
  readonly mulSymbol: string;
  readonly mulSymbolNumbers: string;
  readonly symbolNames: ReadonlyMap<Expr, string>;
  readonly rootNotation: boolean;
  readonly imaginaryUnit: string;
  readonly gothicReIm: boolean;
  readonly comma: boolean;
  readonly parenthesizeSuper: boolean;
  readonly diffOperator: string;
  readonly disableSplitSuperSub: boolean;
  readonly fullPrec: boolean;
}

const MUL_SYMBOLS: Readonly<Record<string, string>> = { ldot: ' \\,.\\, ', dot: ' \\cdot ', times: ' \\times ' };
const IMAGINARY_UNITS: Readonly<Record<string, string>> = { i: 'i', ri: '\\mathrm{i}', ti: '\\text{i}', j: 'j', rj: '\\mathrm{j}', tj: '\\text{j}' };
const DIFF_OPERATORS: Readonly<Record<string, string>> = { d: 'd', rd: '\\mathrm{d}', td: '\\text{d}' };

/** SymPy LatexPrinter.__init__: the settings with their defaults and derived values. */
function resolveSettings(o: LatexOptions): Settings {
  const mode = o.mode ?? 'plain';
  if (!['plain', 'inline', 'equation', 'equation*'].includes(mode)) throw new RangeError("'mode' must be one of 'inline', 'plain', 'equation' or 'equation*'");
  const decimal = o.decimalSeparator ?? 'period';
  if (!['period', 'comma'].includes(decimal)) throw new RangeError('Unknown Decimal Separator');
  const m = o.mulSymbol;
  // between two numbers a symbol is always shown: a dot unless the symbol itself is visible
  const key = m === undefined || m === '' ? 'dot' : m;
  const numbers = MUL_SYMBOLS[key] ?? (['', '\\', '\\,', '\\:', '\\;', '\\quad'].includes(key.trim()) ? ' \\cdot ' : key);
  const iu = o.imaginaryUnit ?? 'i';
  const dop = o.diffOperator ?? 'd';
  return {
    mode,
    itex: o.itex ?? false,
    foldFracPowers: o.foldFracPowers ?? false,
    foldFuncBrackets: o.foldFuncBrackets ?? false,
    foldShortFrac: o.foldShortFrac ?? mode === 'inline',
    invTrigStyle: o.invTrigStyle ?? 'abbreviated',
    lnNotation: o.lnNotation ?? false,
    longFracRatio: o.longFracRatio,
    matDelim: o.matDelim ?? '[',
    matStr: o.matStr,
    mulSymbol: m === undefined ? ' ' : (MUL_SYMBOLS[m] ?? m),
    mulSymbolNumbers: numbers,
    symbolNames: o.symbolNames ?? new Map(),
    rootNotation: o.rootNotation ?? true,
    imaginaryUnit: IMAGINARY_UNITS[iu] ?? iu,
    gothicReIm: o.gothicReIm ?? false,
    comma: decimal === 'comma',
    parenthesizeSuper: o.parenthesizeSuper ?? true,
    diffOperator: DIFF_OPERATORS[dop] ?? dop,
    disableSplitSuperSub: o.disableSplitSuperSub ?? false,
    fullPrec: o.fullPrec ?? false,
  };
}

const DEFAULT_SETTINGS = resolveSettings({});
/** The settings of the print in progress (SymPy `self._settings`). */
let settings: Settings = DEFAULT_SETTINGS;
/** The nesting depth of public calls: a call made while printing (by a node's printLatex) keeps the settings. */
let depth = 0;

// ---------------------------------------------------------------------------
// Symbols
// ---------------------------------------------------------------------------

const GREEK = new Set([
  'alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lambda',
  'mu', 'nu', 'xi', 'omicron', 'pi', 'rho', 'sigma', 'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega',
]);

const TEX_GREEK: Record<string, string> = {
  Alpha: '\\mathrm{A}', Beta: '\\mathrm{B}', Gamma: '\\Gamma', Delta: '\\Delta', Epsilon: '\\mathrm{E}',
  Zeta: '\\mathrm{Z}', Eta: '\\mathrm{H}', Theta: '\\Theta', Iota: '\\mathrm{I}', Kappa: '\\mathrm{K}',
  Lambda: '\\Lambda', Mu: '\\mathrm{M}', Nu: '\\mathrm{N}', Xi: '\\Xi', omicron: 'o', Omicron: '\\mathrm{O}',
  Pi: '\\Pi', Rho: '\\mathrm{P}', Sigma: '\\Sigma', Tau: '\\mathrm{T}', Upsilon: '\\Upsilon', Phi: '\\Phi',
  Chi: '\\mathrm{X}', Psi: '\\Psi', Omega: '\\Omega', lamda: '\\lambda', Lamda: '\\Lambda', khi: '\\chi',
  Khi: '\\mathrm{X}', varepsilon: '\\varepsilon', varkappa: '\\varkappa', varphi: '\\varphi', varpi: '\\varpi',
  varrho: '\\varrho', varsigma: '\\varsigma', vartheta: '\\vartheta',
};

const OTHER_SYMBOLS = new Set([
  'aleph', 'beth', 'daleth', 'gimel', 'ell', 'eth', 'hbar', 'hslash', 'mho', 'wp', 'partial', 'nabla', 'infty',
]);

const MODIFIERS: [string, (s: string) => string][] = (
  [
    ['mathring', (s) => `\\mathring{${s}}`],
    ['ddddot', (s) => `\\ddddot{${s}}`],
    ['dddot', (s) => `\\dddot{${s}}`],
    ['ddot', (s) => `\\ddot{${s}}`],
    ['dot', (s) => `\\dot{${s}}`],
    ['check', (s) => `\\check{${s}}`],
    ['breve', (s) => `\\breve{${s}}`],
    ['acute', (s) => `\\acute{${s}}`],
    ['grave', (s) => `\\grave{${s}}`],
    ['tilde', (s) => `\\tilde{${s}}`],
    ['hat', (s) => `\\hat{${s}}`],
    ['bar', (s) => `\\bar{${s}}`],
    ['vec', (s) => `\\vec{${s}}`],
    ['prime', (s) => `{${s}}'`],
    ['prm', (s) => `{${s}}'`],
    ['bold', (s) => `\\boldsymbol{${s}}`],
    ['bm', (s) => `\\boldsymbol{${s}}`],
    ['cal', (s) => `\\mathcal{${s}}`],
    ['scr', (s) => `\\mathscr{${s}}`],
    ['frak', (s) => `\\mathfrak{${s}}`],
    ['norm', (s) => `\\left\\|{${s}}\\right\\|`],
    ['avg', (s) => `\\left\\langle{${s}}\\right\\rangle`],
    ['abs', (s) => `\\left|{${s}}\\right|`],
    ['mag', (s) => `\\left|{${s}}\\right|`],
  ] as [string, (s: string) => string][]
).sort((a, b) => b[0].length - a[0].length);

function translate(s: string): string {
  const g = TEX_GREEK[s];
  if (g) return g;
  if (GREEK.has(s.toLowerCase())) return `\\${s.toLowerCase()}`;
  if (OTHER_SYMBOLS.has(s)) return `\\${s}`;
  for (const [key, f] of MODIFIERS) {
    if (s.toLowerCase().endsWith(key) && s.length > key.length) return f(translate(s.slice(0, -key.length)));
  }
  return s;
}

/** SymPy `split_super_sub`. */
export function splitSuperSub(text: string): [string, string[], string[]] {
  let pos = 0;
  let name: string | undefined;
  const supers: string[] = [];
  const subs: string[] = [];
  while (pos < text.length) {
    let start = pos + 1;
    if (text.slice(pos, pos + 2) === '__') start += 1;
    let posHat = text.indexOf('^', start);
    if (posHat < 0) posHat = text.length;
    let posUsc = text.indexOf('_', start);
    if (posUsc < 0) posUsc = text.length;
    const next = Math.min(posHat, posUsc);
    const part = text.slice(pos, next);
    pos = next;
    if (name === undefined) name = part;
    else if (part.startsWith('^')) supers.push(part.slice(1));
    else if (part.startsWith('__')) supers.push(part.slice(2));
    // every later part starts at a '^' or '_'
    else subs.push(part.slice(1));
  }
  name ??= '';
  const m = /^([^\W\d_]+)(\d+)$/u.exec(name);
  if (m) {
    name = at(m, 1);
    subs.unshift(at(m, 2));
  }
  return [name, supers, subs];
}

function symbolLatex(text: string): string {
  if (text.includes('{')) return text;
  // SymPy disable_split_super_sub: the name as it is, its _ and ^ escaped
  const [name, supers, subs] = settings.disableSplitSuperSub ? [text.replace(/_/g, '\\_').replace(/\^/g, '\\^'), [], []] : splitSuperSub(text);
  let out = translate(name);
  if (supers.length) out += `^{${supers.map(translate).join(' ')}}`;
  if (subs.length) out += `_{${subs.map(translate).join(' ')}}`;
  return out;
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** SymPy `precedence_traditional`: the LaTeX precedence a node declares, else the str precedence. */
const precedence = (e: Expr): number => declaredPrecedence(e, 'latexPrecedence') ?? strPrecedence(e);

const isExp = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
const addParens = (s: string) => `\\left(${s}\\right)`;

function parenthesize(e: Expr, level: number): string {
  const s = texOf(e);
  return precedence(e) <= level ? addParens(s) : s;
}

/** Whether a node of the tree satisfies the predicate (SymPy `expr.has(cls)`). */
const contains = (e: Expr, pred: (x: Expr) => boolean): boolean => pred(e) || e.args.some((a) => contains(a, pred));
const isModNode = (x: Expr): boolean => (x instanceof Fn || x instanceof ExtensionExpr) && x.name === 'Mod';
const isLimitsNode = (x: Expr): boolean => x instanceof Integral || x instanceof Concrete;

/**
 * SymPy `_needs_mul_brackets`: a factor printed in parentheses inside a
 * product (`first` and `last` say where it appears).
 */
function needsMulBrackets(e: Expr, first: boolean, last: boolean): boolean {
  if (e instanceof Mul) {
    if (!first && startsNegative(e)) return true;
  } else if (precedence(e) < PREC.MUL || e instanceof Rel) return true;
  if (e instanceof Piecewise || contains(e, isModNode)) return true;
  return !last && contains(e, isLimitsNode);
}

const ACCEPTED_FUNCTIONS = new Set([
  'arcsin', 'arccos', 'arctan', 'sin', 'cos', 'tan', 'sinh', 'cosh', 'tanh', 'sqrt', 'ln', 'log',
  'sec', 'csc', 'cot', 'coth', 're', 'im', 'frac', 'root', 'arg',
]);

/** SymPy `_hprint_Function`: the name with sub- and superscripts, in \operatorname unless LaTeX knows it. */
function hprintFunction(name0: string): string {
  const name = symbolLatex(name0);
  if (ACCEPTED_FUNCTIONS.has(name)) return `\\${name}`;
  const sup = name.indexOf('^');
  const sub = name.indexOf('_');
  if (name.length === 1 || name.startsWith('\\') || sub === 1 || sup === 1) return name;
  const cut = Math.min(...[sup, sub].filter((i) => i > 0));
  return Number.isFinite(cut) ? `\\operatorname{${name.slice(0, cut)}}${name.slice(cut)}` : `\\operatorname{${name}}`;
}

/** SymPy `parenthesize_super`: a superscripted base in parentheses (or braces with parenthesizeSuper false). */
const parenthesizeSuper = (s: string) => (!s.includes('^') ? s : settings.parenthesizeSuper ? addParens(s) : `{${s}}`);

/** SymPy `_do_exponent`. */
const doExponent = (tex: string, exp?: string): string => (exp !== undefined ? `\\left(${tex}\\right)^{${exp}}` : tex);
/** `tex^{exp}` when raised to a power. */
const withExponent = (tex: string, exp?: string): string => (exp !== undefined ? `${tex}^{${exp}}` : tex);
/** `head^{exp}` followed by the arguments in parentheses (SymPy _hprint_one_arg_func and the like). */
const headArgs = (head: string, args: readonly Expr[], exp?: string): string => `${withExponent(head, exp)}\\left(${args.map(texOf).join(', ')}\\right)`;
/** SymPy `__print_number_polynomial`: B_{n}, or B_{n}\left(x\right) for the polynomial. */
function numberPolynomial(letter: string, args: readonly Expr[], exp?: string): string {
  const head = withExponent(`${letter}_{${texOf(at(args, 0))}}`, exp);
  return args.length === 2 ? `${head}\\left(${texOf(at(args, 1))}\\right)` : head;
}

const ONE_ARG_HEADS: Partial<Record<string, string>> = {
  gamma: '\\Gamma',
  zeta: '\\zeta',
  Chi: '\\operatorname{Chi}',
  fresnels: 'S',
  fresnelc: 'C',
  lowergamma: '\\gamma',
  uppergamma: '\\Gamma',
  mobius: '\\mu',
};
const NUMBER_POLYNOMIALS: Partial<Record<string, string>> = { bernoulli: 'B', genocchi: 'G', bell: 'B', fibonacci: 'F', tribonacci: 'T' };
const PAREN_POWER_HEADS: Partial<Record<string, string>> = { totient: '\\phi', reduced_totient: '\\lambda', primenu: '\\nu', primeomega: '\\Omega' };
const ORTHOPOLY_LETTERS: Record<'jacobi' | 'gegenbauer' | 'chebyshevt' | 'chebyshevu' | 'legendre' | 'assoc_legendre' | 'hermite' | 'laguerre' | 'assoc_laguerre', string> = {
  jacobi: 'P',
  gegenbauer: 'C',
  chebyshevt: 'T',
  chebyshevu: 'U',
  legendre: 'P',
  assoc_legendre: 'P',
  hermite: 'H',
  laguerre: 'L',
  assoc_laguerre: 'L',
};
const BESSEL_SYMBOLS: Partial<Record<string, string>> = { besselj: 'J', bessely: 'Y', besseli: 'I', besselk: 'K', jn: 'j', yn: 'y' };

/** SymPy `_hprint_vec` of the LaTeX printer. */
const hprintVec = (v: readonly Expr[]): string => v.map(texOf).join(', ');

/** The members of a meijerg node the printers use (functions/ is a higher layer). */
interface MeijerLike {
  readonly argument: Expr;
  readonly an: readonly Expr[];
  readonly aother: readonly Expr[];
  readonly bm: readonly Expr[];
  readonly bother: readonly Expr[];
}
const isMeijer = (e: Expr): e is ExtensionExpr & MeijerLike => e instanceof ExtensionExpr && e.name === 'meijerg' && 'an' in e && 'bother' in e;

/**
 * SymPy's printers of the functions that are function nodes here and
 * defined functions or extension nodes elsewhere (_print_SingularityFunction,
 * _print_Heaviside, _print_DiracDelta, _print_polylog, _print_lerchphi,
 * _print_elliptic_*, _print_betainc, _print_dirichlet_eta, _print_stieltjes),
 * optionally raised to a power; undefined for the other names.
 */
function printNamedFunction(name: string, args: readonly Expr[], exp?: string): string | undefined {
  const sup = exp !== undefined ? `^{${exp}}` : '';
  const l = args.map(texOf);
  const [a, b, c] = [l[0] ?? '', l[1] ?? '', l[2] ?? ''];
  switch (name) {
    case 'SingularityFunction': {
      const shift = texOf(impl.add(at(args, 0), impl.mul(-1, at(args, 1))));
      const power = texOf(at(args, 2));
      return exp === undefined ? `{\\left\\langle ${shift} \\right\\rangle}^{${power}}` : `{\\left({\\langle ${shift} \\rangle}^{${power}}\\right)}^{${exp}}`;
    }
    case 'Heaviside': {
      // SymPy Heaviside.pargs: the arguments without the default value 1/2 at 0
      const h0 = args[1];
      const pargs = h0 instanceof Rational && h0.p === 1n && h0.q === 2n ? [a] : l;
      return doExponent(`\\theta\\left(${pargs.join(', ')}\\right)`, exp);
    }
    case 'DiracDelta': {
      const k = args[1];
      const tex = k === undefined || (k instanceof Rational && k.isZero) ? `\\delta\\left(${a}\\right)` : `\\delta^{\\left( ${b} \\right)}\\left( ${a} \\right)`;
      return doExponent(tex, exp);
    }
    case 'polylog':
      return `\\operatorname{Li}_{${a}}${sup}\\left(${b}\\right)`;
    case 'lerchphi':
      return `\\Phi${sup}\\left(${a}, ${b}, ${c}\\right)`;
    case 'elliptic_k':
      return `K${sup}\\left(${a}\\right)`;
    case 'elliptic_f':
      return `F${sup}\\left(${a}\\middle| ${b}\\right)`;
    case 'elliptic_e':
      return `E${sup}${args.length === 2 ? `\\left(${a}\\middle| ${b}\\right)` : `\\left(${a}\\right)`}`;
    case 'elliptic_pi':
      return `\\Pi${sup}${args.length === 3 ? `\\left(${a}; ${b}\\middle| ${c}\\right)` : `\\left(${a}\\middle| ${b}\\right)`}`;
    case 'betainc':
    case 'betainc_regularized':
      return `\\operatorname{${name === 'betainc' ? 'B' : 'I'}}_{(${c}, ${texOf(at(args, 3))})}${sup}\\left(${a}, ${b}\\right)`;
    case 'dirichlet_eta':
      // SymPy prints only the first argument, \eta\left(s\right) also for dirichlet_eta(s, a): the
      // second one is kept here, as the two functions differ
      return `\\eta${sup}\\left(${l.join(', ')}\\right)`;
    case 'stieltjes': {
      const tex = args.length === 2 ? `_{${a}}\\left(${b}\\right)` : `_{${a}}`;
      return `\\gamma${tex}${sup}`;
    }
    default:
      return undefined;
  }
}

/** SymPy `_print_meijerg`. */
function printMeijer(e: MeijerLike, exp?: string): string {
  const tex = `{G_{${e.an.length + e.aother.length}, ${e.bm.length + e.bother.length}}^{${e.bm.length}, ${e.an.length}}\\left(\\begin{matrix} ${hprintVec(e.an)} & ${hprintVec(e.aother)} \\\\${hprintVec(e.bm)} & ${hprintVec(e.bother)} \\end{matrix} \\middle| {${texOf(e.argument)}} \\right)}`;
  return exp !== undefined ? `{${tex}}^{${exp}}` : tex;
}

/** SymPy `_print_SeqFormula` (and SeqPer, SeqAdd, SeqMul). */
function printSequence(e: ExtensionExpr & Parameters<typeof sequencePrintset>[0]): string {
  if (hasSymbolicBounds(e)) {
    // only a SeqFormula has a formula to print (SymPy fails for the others)
    if (e.name !== 'SeqFormula') return e.printLatex(texOf);
    return `\\left\\{${texOf(at(e.args, 3))}\\right\\}_{${texOf(at(e.args, 0))}=${texOf(e.start)}}^{${texOf(e.stop)}}`;
  }
  return `\\left[${sequencePrintset(e).map((t) => (t === DOTS ? '\\ldots' : texOf(t))).join(', ')}\\right]`;
}

/** Print a function, optionally raised to a power (SymPy prints sin(x)**2 as \sin^{2}...). */
function printFunction(e: Fn, exp?: string): string {
  const args = e.args;
  const x0 = at(args, 0);
  const a = texOf(x0);
  const head = ONE_ARG_HEADS[e.name];
  if (head !== undefined) return headArgs(head, args, exp);
  const letter = NUMBER_POLYNOMIALS[e.name];
  if (letter !== undefined) return numberPolynomial(letter, args, exp);
  const parenHead = PAREN_POWER_HEADS[e.name];
  if (parenHead !== undefined) return doExponent(`${parenHead}\\left(${a}\\right)`, exp);
  const bessel = BESSEL_SYMBOLS[e.name];
  if (bessel !== undefined) {
    // SymPy _hprint_BesselBase: J^{exp}_{\nu}\left(z\right)
    return `${withExponent(bessel, exp)}_{${a}}\\left(${texOf(at(args, 1))}\\right)`;
  }
  const named = printNamedFunction(e.name, args, exp);
  if (named !== undefined) return named;
  switch (e.name) {
    case 'abs':
      return withExponent(`\\left|{${a}}\\right|`, exp);
    case 'adjoint': {
      const base = `${parenthesize(x0, PREC.POW)}^{\\dagger}`;
      return doExponent(base, exp);
    }
    case 'conjugate':
      return withExponent(`\\overline{${a}}`, exp);
    case 're':
    case 'im': {
      // SymPy _print_re / _print_im: the argument parenthesized at atom level
      const head = settings.gothicReIm ? (e.name === 're' ? '\\Re' : '\\Im') : `\\operatorname{${e.name}}`;
      return doExponent(`${head}{${parenthesize(x0, PREC.ATOM)}}`, exp);
    }
    case 'log':
      return withExponent(`\\${settings.lnNotation ? 'ln' : 'log'}{\\left(${a} \\right)}`, exp);
    case 'floor':
      return withExponent(`\\left\\lfloor{${a}}\\right\\rfloor`, exp);
    case 'ceiling':
      return withExponent(`\\left\\lceil{${a}}\\right\\rceil`, exp);
    case 'frac':
      return withExponent(`\\operatorname{frac}{\\left(${a}\\right)}`, exp);
    case 'factorial':
      return withExponent(`${parenthesize(x0, PREC.FUNC)}!`, exp);
    case 'factorial2':
      return withExponent(`${parenthesize(x0, PREC.FUNC)}!!`, exp);
    case 'subfactorial':
      return doExponent(`!${parenthesize(x0, PREC.FUNC)}`, exp);
    case 'catalan':
      return withExponent(`C_{${a}}`, exp);
    case 'lucas':
      return withExponent(`L_{${a}}`, exp);
    case 'binomial':
      return withExponent(`{\\binom{${a}}{${texOf(at(args, 1))}}}`, exp);
    case 'beta':
      return headArgs('\\operatorname{B}', args.length === 1 ? [x0, x0] : args, exp);
    case 'expint':
      return `\\operatorname{E}_{${a}}${withExponent('', exp)}\\left(${texOf(at(args, 1))}\\right)`;
    case 'ff':
      return doExponent(`{\\left(${a}\\right)}_{${parenthesize(at(args, 1), PREC.FUNC)}}`, exp);
    case 'rf':
      return doExponent(`{${parenthesize(x0, PREC.FUNC)}}^{\\left(${texOf(at(args, 1))}\\right)}`, exp);
    case 'LambertW': {
      const k = args[1];
      return `W${withExponent('', exp)}${k ? `_{${texOf(k)}}` : ''}\\left(${a}\\right)`;
    }
    case 'euler': {
      const tex = withExponent(`E_{${a}}`, exp);
      const z = args[1];
      return z ? `${tex}\\left(${texOf(z)}\\right)` : tex;
    }
    case 'divisor_sigma': {
      const k = args[1];
      return `\\sigma${withExponent('', exp)}${k ? `_${texOf(k)}` : ''}\\left(${a}\\right)`;
    }
    case 'KroneckerDelta': {
      const b = at(args, 1);
      const atomic = (v: Expr) => v instanceof Sym || isNum(v) || v instanceof Constant || v instanceof Special;
      const tex = atomic(x0) && atomic(b) ? `\\delta_{${a} ${texOf(b)}}` : `\\delta_{${a}, ${texOf(b)}}`;
      return doExponent(tex, exp);
    }
    case 'Min':
    case 'Max': {
      // SymPy _hprint_variadic_function: the arguments in default_sort_key order
      const sorted = [...args].sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
      return withExponent(`\\${e.name.toLowerCase()}\\left(${sorted.map(texOf).join(', ')}\\right)`, exp);
    }
    case 'exp_polar':
      // SymPy _print_ExpBase
      return doExponent(`e^{${a}}`, exp);
    case 'polar_lift':
      return `\\operatorname{polar\\_lift}${withExponent('', exp)}{\\left(${a} \\right)}`;
    case 'jacobi':
    case 'gegenbauer':
    case 'chebyshevt':
    case 'chebyshevu':
    case 'legendre':
    case 'assoc_legendre':
    case 'hermite':
    case 'laguerre':
    case 'assoc_laguerre': {
      // SymPy _print_jacobi, _print_gegenbauer, ...: the letter, the degree, the parameters
      const letter = ORTHOPOLY_LETTERS[e.name];
      const params = args.slice(1, -1).map(texOf);
      const sup = params.length ? `^{\\left(${params.join(',')}\\right)}` : '';
      const tex = `${letter}_{${a}}${sup}\\left(${texOf(at(args, args.length - 1))}\\right)`;
      return exp !== undefined ? `\\left(${tex}\\right)^{${exp}}` : tex;
    }
    case 'hankel1':
    case 'hankel2':
    case 'hn1':
    case 'hn2': {
      // SymPy _hprint_BesselBase with a symbol that has a superscript: the power wraps the call
      const tex = `${e.name.startsWith('hankel') ? 'H' : 'h'}^{(${e.name.slice(-1)})}_{${a}}\\left(${texOf(at(args, 1))}\\right)`;
      return exp !== undefined ? `\\left(${tex}\\right)^{${exp}}` : tex;
    }
    case 'Ynm':
    case 'Znm': {
      const tex = `${e.name.charAt(0)}_{${a}}^{${texOf(at(args, 1))}}\\left(${texOf(at(args, 2))},${texOf(at(args, 3))}\\right)`;
      return exp !== undefined ? `\\left(${tex}\\right)^{${exp}}` : tex;
    }
    case 'mathieuc':
    case 'mathieus':
    case 'mathieucprime':
    case 'mathieusprime': {
      // SymPy __print_mathieu_functions: the exponent follows the arguments
      const sup = e.name.endsWith('prime') ? '^{\\prime}' : '';
      return `${e.name.charAt(7).toUpperCase()}${sup}\\left(${args.map(texOf).join(', ')}\\right)${exp !== undefined ? `^{${exp}}` : ''}`;
    }
    case 'airyai':
    case 'airybi':
    case 'airyaiprime':
    case 'airybiprime': {
      const base = e.name.startsWith('airyai') ? 'Ai' : 'Bi';
      const tex = `\\left(${a}\\right)`;
      // SymPy _hprint_airy_prime braces the primed name before the exponent: {Ai^\prime}^{2}
      if (!e.name.endsWith('prime')) return `${withExponent(base, exp)}${tex}`;
      return exp !== undefined ? `{${base}^\\prime}^{${exp}}${tex}` : `${base}^\\prime${tex}`;
    }
    default:
      return printPlainFunction(e.name, args, exp);
  }
}

const INV_TRIG = new Set(['asin', 'acos', 'atan', 'acsc', 'asec', 'acot', 'asinh', 'acosh', 'atanh', 'acsch', 'asech', 'acoth']);

/** SymPy `_needs_brackets`: anything but a nonnegative integer or an atom that is not a rational. */
function needsBrackets(e: Expr): boolean {
  if (e instanceof Rational) return !(e.isInteger && e.p >= 0n);
  return !(e.isAtom || e instanceof Constant || e instanceof Special);
}

/** SymPy `_needs_function_brackets`: an argument that cannot follow the function name without brackets. */
function needsFunctionBrackets(e: Expr): boolean {
  if (!needsBrackets(e)) return false;
  if (e instanceof Mul) return e.args.some((a) => a instanceof Fn || a instanceof UndefFn || isExp(a));
  if (e instanceof Pow) return isExp(e) || needsBrackets(e.base);
  // sums and functions always need brackets
  return e instanceof Add || e instanceof Fn || e instanceof UndefFn;
}

/**
 * SymPy `_print_Function` for functions without their own printer: the
 * inverse trigonometric style, folded brackets and the exponent.
 */
function printPlainFunction(name0: string, args: readonly Expr[], exp?: string): string {
  let func = name0;
  let fold = settings.foldFuncBrackets && args.length === 1 && !needsFunctionBrackets(at(args, 0));
  let power = false;
  if (INV_TRIG.has(func) && settings.invTrigStyle !== 'abbreviated') {
    if (settings.invTrigStyle === 'full') func = (func.endsWith('h') ? 'ar' : 'arc') + func.slice(1);
    else {
      func = func.slice(1);
      power = true;
      // never folded when raised to a power
      if (exp !== undefined) fold = false;
    }
  }
  let name: string;
  if (power) name = ACCEPTED_FUNCTIONS.has(func) ? `\\${func}^{-1}` : `\\operatorname{${func}}^{-1}`;
  else if (exp !== undefined) name = `${parenthesizeSuper(hprintFunction(func))}^{${exp}}`;
  else name = hprintFunction(func);
  const body = args.map(texOf).join(',');
  if (fold) name += ACCEPTED_FUNCTIONS.has(func) ? ` {${body}}` : body;
  else name += `{\\left(${body} \\right)}`;
  return power && exp !== undefined ? `${name}^{${exp}}` : name;
}

/** SymPy `fraction(expr, exact=True)`. */
function fraction(e: Expr): [Expr[], Expr[]] {
  const numer: Expr[] = [];
  const denom: Expr[] = [];
  for (const term of e instanceof Mul ? e.args : [e]) {
    if (term instanceof Pow && term.isCommutative) {
      const [b, x] = term.args;
      if (isNegative(x)) {
        if (x instanceof Rational && x.p === -1n && x.q === 1n) denom.push(b);
        else if (impl.freeSymbols(x).size === 0) denom.push(pow(b, mul(-1, x)));
        else numer.push(term);
      } else numer.push(term);
    } else if (term instanceof Rational && !term.isInteger) {
      if (term.p !== 1n) numer.push(Rational.of(term.p));
      denom.push(Rational.of(term.q));
    } else numer.push(term);
  }
  return [numer, denom];
}

const BETWEEN_NUMBERS: [RegExp, RegExp] = [/[0-9][} ]*$/, /^(\d|\\frac{\d+}{\d+})/];

function convertArgs(args: readonly Expr[]): string {
  let tex = '';
  let last = '';
  args.forEach((term, i) => {
    let t = texOf(term);
    if (needsMulBrackets(term, i === 0, i === args.length - 1)) t = addParens(t);
    if (BETWEEN_NUMBERS[0].test(last) && BETWEEN_NUMBERS[1].test(str(term))) tex += settings.mulSymbolNumbers;
    else if (tex) tex += settings.mulSymbol;
    tex += t;
    last = t;
  });
  return tex;
}

function convertFactors(fs: Expr[]): string {
  if (fs.length === 0) return '1';
  if (fs.length === 1) return texOf(at(fs, 0));
  return convertArgs(asOrderedFactors(new Mul(fs)));
}

const words = (t: string): number => t.split(/\s+/).filter(Boolean).length;
const product = (fs: readonly Expr[]): Expr => (fs.length === 1 ? at(fs, 0) : new Mul(fs));

/**
 * SymPy `_print_Mul` of a quotient: `\\frac{numer}{denom}`, a short fraction
 * `numer / denom` (fold_short_frac) or a long numerator split off the
 * fraction (long_frac_ratio).
 */
function printFraction(numer: Expr[], denom: Expr[]): string {
  const snumer = convertFactors(numer);
  const sdenom = convertFactors(denom);
  const ldenom = words(sdenom);
  const ratio = settings.longFracRatio;
  const sep = settings.mulSymbol;
  const n = numer.length === 0 ? S.One : product(numer);
  if (settings.foldShortFrac && ldenom <= 2 && !sdenom.includes('^')) {
    return needsMulBrackets(n, false, false) ? `\\left(${snumer}\\right) / ${sdenom}` : `${snumer} / ${sdenom}`;
  }
  if (ratio === undefined || words(snumer) <= ratio * ldenom) return `\\frac{${snumer}}{${sdenom}}`;
  if (needsMulBrackets(n, false, true)) return `\\frac{1}{${sdenom}}${sep}\\left(${snumer}\\right)`;
  if (!(n instanceof Mul)) return `\\frac{1}{${sdenom}}${sep}${snumer}`;
  // split a long numerator: the factors that keep it short stay in the fraction
  const a: Expr[] = [];
  const b: Expr[] = [];
  for (const x of n.args) {
    if (needsMulBrackets(x, false, false) || words(convertFactors([...a, x])) > ratio * ldenom || (!x.isCommutative && b.some((y) => !y.isCommutative))) b.push(x);
    else a.push(x);
  }
  const sb = convertFactors(b);
  return `\\frac{${convertFactors(a)}}{${sdenom}}${sep}${needsMulBrackets(product(b), false, true) ? `\\left(${sb}\\right)` : sb}`;
}

function printMulLike(e: Expr): string {
  let expr = e;
  let tex = '';
  let includeParens = false;
  if (startsNegative(expr)) {
    const [c, rest] = splitCoeff(expr);
    const pc = numNeg(c);
    // a product led by -oo has no numeric coefficient: SymPy prints -(-oo*x) = oo*x
    if (!c.isNegative) expr = mul(-1, expr);
    else expr = pc instanceof Rational && pc.isOne ? rest : new Mul([pc, ...(rest instanceof Mul ? rest.args : [rest])]);
    tex = '- ';
    if (expr instanceof Add) {
      tex += '(';
      includeParens = true;
    }
  }
  const [numer, denom] = fraction(expr);
  if (denom.length === 0) {
    tex += expr instanceof Mul ? convertArgs(asOrderedFactors(expr)) : texOf(expr);
  } else {
    tex += printFraction(numer, denom);
  }
  if (includeParens) tex += ')';
  return tex;
}

/** A function raised to a power, the exponent printed by the function (SymPy `_print_Function(expr, exp)`). */
const printPowOfFunction = (b: Fn | UndefFn, exp: string): string => (b instanceof Fn ? printFunction(b, exp) : printPlainFunction(b.name, b.args, exp));

function printPow(e: Pow): string {
  const [b, x] = e.args;
  if (isExp(e)) return `e^{${texOf(x)}}`;
  if (x instanceof Rational) {
    const p = x.p < 0n ? -x.p : x.p;
    if (p === 1n && x.q !== 1n && settings.rootNotation) {
      const base = texOf(b);
      const tex = x.q === 2n ? `\\sqrt{${base}}` : settings.itex ? `\\root{${x.q}}{${base}}` : `\\sqrt[${x.q}]{${base}}`;
      return x.p < 0n ? `\\frac{1}{${tex}}` : tex;
    }
    if (settings.foldFracPowers && x.q !== 1n) {
      const folded = `${x.p}/${x.q}`;
      if (b instanceof Fn || b instanceof UndefFn) return printPowOfFunction(b, folded);
      const base = parenthesize(b, PREC.POW);
      return `${b instanceof Sym ? parenthesizeSuper(base) : base}^{${folded}}`;
    }
    if (x.p < 0n && b.isCommutative) return printMulLike(e);
  }
  if (b instanceof Fn || b instanceof UndefFn) return printPowOfFunction(b, texOf(x));
  if (b instanceof ExtensionExpr) {
    const named = printNamedFunction(b.name, b.args, texOf(x));
    if (named !== undefined) return named;
    if (isMeijer(b)) return printMeijer(b, texOf(x));
    // SymPy _print_hyper: the braced form raised to the power
    if (b.name === 'hyper') return `{${texOf(b)}}^{${texOf(x)}}`;
  }
  let base = parenthesize(b, PREC.POW);
  if (b instanceof Sym) base = parenthesizeSuper(base);
  else if (b instanceof Float) base = `{${base}}`;
  return `${base}^{${texOf(x)}}`;
}

function printAdd(e: Add): string {
  let tex = '';
  asOrderedTerms(e).forEach((term0, i) => {
    let term = term0;
    if (i > 0) {
      if (startsNegative(term)) {
        tex += ' - ';
        term = mul(-1, term);
      } else tex += ' + ';
    }
    const t = texOf(term);
    tex += term instanceof Add ? addParens(t) : t;
  });
  return tex;
}

function floatLatex(f: Float): string {
  const s = floatString(f, !settings.fullPrec);
  const sep = (t: string): string => (settings.comma ? t.replace('.', '{,}') : t);
  const k = s.indexOf('e');
  if (k < 0) return sep(s);
  const exp = s.slice(k + 1);
  return `${sep(s.slice(0, k))}${settings.mulSymbolNumbers}10^{${exp.startsWith('+') ? exp.slice(1) : exp}}`;
}

function texOf(e: Expr): string {
  if (e instanceof ExtensionExpr) {
    const named = printNamedFunction(e.name, e.args);
    if (named !== undefined) return named;
    if (isMeijer(e)) return printMeijer(e);
    if (isSequence(e)) return printSequence(e);
    if (e.name === 'EmptySequence') return '\\text{EmptySequence}';
  }
  if (e instanceof ExtensionExpr || e instanceof BoolOp) return e.printLatex(texOf);
  if (e instanceof Rational) {
    if (e.q === 1n) return `${e.p}`;
    const [sign, p] = e.p < 0n ? ['- ', -e.p] : ['', e.p];
    return settings.foldShortFrac ? `${sign}${p} / ${e.q}` : `${sign}\\frac{${p}}{${e.q}}`;
  }
  if (e instanceof Float) return floatLatex(e);
  if (e instanceof Sym) return symbolName(e) ?? e.latexForm ?? symbolLatex(e.name);
  if (e instanceof Constant) {
    return { pi: '\\pi', E: 'e', I: settings.imaginaryUnit, EulerGamma: '\\gamma', Catalan: 'G', GoldenRatio: '\\phi', TribonacciConstant: '\\text{TribonacciConstant}' }[e.name];
  }
  if (e instanceof Special) {
    return { oo: '\\infty', '-oo': '-\\infty', zoo: '\\tilde{\\infty}', nan: '\\text{NaN}' }[e.name];
  }
  if (e instanceof Fn) return printFunction(e);
  if (e instanceof Add) return printAdd(e);
  if (e instanceof Mul) return printMulLike(e);
  if (e instanceof Pow) return printPow(e);
  if (e instanceof BoolAtom) return e.value ? '\\text{True}' : '\\text{False}';
  if (e instanceof Rel) {
    const op = { Eq: '=', Ne: '\\neq', Lt: settings.itex ? '\\lt' : '<', Le: '\\leq', Gt: settings.itex ? '\\gt' : '>', Ge: '\\geq' }[e.op];
    return `${texOf(e.lhs)} ${op} ${texOf(e.rhs)}`;
  }
  if (e instanceof Piecewise) {
    const pairs = e.pairs;
    const parts = pairs.map(([x, c], i) =>
      i === pairs.length - 1 && c instanceof BoolAtom && c.value
        ? `${texOf(x)} & \\text{otherwise}`
        : `${texOf(x)} & \\text{for}\\: ${texOf(c)}`,
    );
    return `\\begin{cases} ${parts.join(' \\\\')} \\end{cases}`;
  }
  if (e instanceof UndefFn) return printPlainFunction(e.name, e.args);
  if (e instanceof Derivative) {
    const partial = impl.freeSymbols(e.expr).size > 1;
    const d = partial ? '\\partial' : settings.diffOperator;
    let tex = '';
    let dim = 0;
    for (const [v, n] of [...e.variableCount].reverse()) {
      dim += n;
      tex += n === 1 ? `${d} ${texOf(v)}` : `${d} ${parenthesizeSuper(texOf(v))}^{${n}}`;
    }
    const head = dim === 1 ? `\\frac{${d}}{${tex}}` : `\\frac{${d}^{${dim}}}{${tex}}`;
    const body = precedence(e.expr) < PREC.MUL ? addParens(texOf(e.expr)) : texOf(e.expr);
    return `${head} ${body}`;
  }
  if (e instanceof Limit) {
    // SymPy _print_Limit: no direction at an infinite point, a sum or product body in parentheses without a space
    const f = e.expr;
    const p = e.point;
    const d = e.dir === '+-' || (p instanceof Special && (p.name === 'oo' || p.name === '-oo')) ? '' : `^${e.dir}`;
    const head = `\\lim_{${texOf(e.variable)} \\to ${texOf(p)}${d}}`;
    return f instanceof Add || f instanceof Mul ? `${head}${addParens(texOf(f))}` : `${head} ${texOf(f)}`;
  }
  if (e instanceof Order) {
    const v = e.variable;
    const p = e.point;
    if (!v || !p || (p instanceof Rational && p.isZero)) return `O\\left(${texOf(e.expr)}\\right)`;
    return `O\\left(${texOf(e.expr)}; ${texOf(v)}\\rightarrow ${texOf(p)}\\right)`;
  }
  if (e instanceof Concrete) {
    // SymPy _print_Sum / _print_Product
    const op = e.kind2 === 'Sum' ? '\\sum' : '\\prod';
    const lims = e.limits;
    const one = lims.length === 1 ? lims[0] : undefined;
    const head =
      one
        ? `${op}_{${texOf(one[0])}=${texOf(one[1])}}^{${texOf(one[2])}} `
        : `${op}_{\\substack{${lims.map(([k, a, b]) => `${texOf(a)} \\leq ${texOf(k)} \\leq ${texOf(b)}`).join('\\\\')}}} `;
    return head + (e.function instanceof Add ? addParens(texOf(e.function)) : texOf(e.function));
  }
  if (e instanceof Integral) {
    // nested integrals: outer signs first, differentials innermost first
    const heads: string[] = [];
    const ds: string[] = [];
    let cur: Expr = e;
    while (cur instanceof Integral) {
      const lim = cur.limits;
      heads.push(lim ? `\\int\\limits_{${texOf(lim[0])}}^{${texOf(lim[1])}}` : '\\int');
      ds.unshift(`\\, d${texOf(cur.variable)}`);
      cur = cur.integrand;
    }
    const body = precedence(cur) < PREC.MUL ? addParens(texOf(cur)) : texOf(cur);
    return `${heads.join('')} ${body}${ds.join('')}`;
  }
  const cls = setClass(e);
  if (cls !== undefined) return printSet(e, cls);
  return e.key;
}

const NAMED_SETS: Partial<Record<string, string>> = {
  EmptySet: '\\emptyset',
  UniversalSet: '\\mathbb{U}',
  Reals: '\\mathbb{R}',
  Rationals: '\\mathbb{Q}',
  Integers: '\\mathbb{Z}',
  Naturals: '\\mathbb{N}',
  Naturals0: '\\mathbb{N}_0',
  Complexes: '\\mathbb{C}',
};
const SET_OPERATORS: Partial<Record<string, string>> = { Union: ' \\cup ', Intersection: ' \\cap ', Complement: ' \\setminus ', SymmetricDifference: ' \\triangle ' };

/** SymPy's set printers (_print_Interval, _print_FiniteSet, _print_Union, ...). */
function printSet(e: Expr, cls: string): string {
  const named = NAMED_SETS[cls];
  if (named !== undefined) return named;
  const op = SET_OPERATORS[cls];
  if (op !== undefined) {
    // set operations bind looser than any argument but another set operation
    const args = cls === 'Complement' || cls === 'SymmetricDifference' ? e.args : setArgsOrdered(e.args);
    return args.map((a) => (SET_OPERATORS[String(setClass(a))] !== undefined ? addParens(texOf(a)) : texOf(a))).join(op);
  }
  switch (cls) {
    case 'Interval': {
      const [a, b, lo, ro] = [at(e.args, 0), at(e.args, 1), at(e.args, 2), at(e.args, 3)];
      if (a.key === b.key) return `\\left\\{${texOf(a)}\\right\\}`;
      const open = (x: Expr) => x instanceof BoolAtom && x.value;
      return `\\left${open(lo) ? '(' : '['}${texOf(a)}, ${texOf(b)}\\right${open(ro) ? ')' : ']'}`;
    }
    case 'Range': {
      const shown = rangePrintForm(e, 3);
      // SymPy _print_symbolic_range: a Range whose elements are unknown
      if ('symbolic' in shown) return `\\text{Range}\\left(${shown.symbolic.map(texOf).join(', ')}\\right)`;
      return `\\left\\{${shown.elements.map((t) => (t === DOTS ? '\\ldots' : texOf(t))).join(', ')}\\right\\}`;
    }
    case 'FiniteSet':
      return `\\left\\{${[...e.args].sort((u, v) => compareKeys(sortKey(u), sortKey(v))).map(texOf).join(', ')}\\right\\}`;
    case 'ImageSet': {
      const [v, expr, base] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
      return `\\left\\{${texOf(expr)}\\; \\middle|\\; ${texOf(v)} \\in ${texOf(base)}\\right\\}`;
    }
    case 'ConditionSet': {
      const [v, cond, base] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
      if (setClass(base) === 'UniversalSet') return `\\left\\{${texOf(v)}\\; \\middle|\\; ${texOf(cond)} \\right\\}`;
      return `\\left\\{${texOf(v)}\\; \\middle|\\; ${texOf(v)} \\in ${texOf(base)} \\wedge ${texOf(cond)} \\right\\}`;
    }
    default:
      // the other sets print themselves (ProductSet, PowerSet, ComplexRegion, ...)
      return 'printLatex' in e && typeof e.printLatex === 'function' ? String(e.printLatex(texOf)) : e.key;
  }
}

/** SymPy `symbol_names`: the LaTeX chosen for a symbol, compared structurally; undefined when none is. */
function symbolName(e: Sym): string | undefined {
  for (const [k, v] of settings.symbolNames) if (k.key === e.key) return v;
  return undefined;
}

/** A matrix as the LaTeX printer sees it (the matrices layer is above this one). */
export interface LatexMatrix {
  readonly rows: number;
  readonly cols: number;
  get(i: number, j: number): Expr;
}

/** What `latex` prints: expressions (numbers are sympified), matrices, lists, dicts, sets, strings, booleans and null (Python None). */
export type LatexPrintable = Expr | number | bigint | boolean | string | null | LatexMatrix | readonly LatexPrintable[] | ReadonlyMap<LatexPrintable, LatexPrintable> | ReadonlySet<LatexPrintable>;

const isMatrixLike = (v: object): v is LatexMatrix => 'rows' in v && 'cols' in v && 'get' in v && typeof v.get === 'function';

/** SymPy `latex_escape`: the LaTeX special characters of a text escaped. */
export function latexEscape(s: string): string {
  let out = s.replace(/\\/g, '\\textbackslash');
  for (const c of '&%$#_{}') out = out.split(c).join(`\\${c}`);
  return out.replace(/~/g, '\\textasciitilde').replace(/\^/g, '\\textasciicircum');
}

/** SymPy `_print_matrix_contents` and `_print_MatrixBase`. */
function printMatrix(m: LatexMatrix): string {
  const lines: string[] = [];
  for (let i = 0; i < m.rows; i++) {
    const row: string[] = [];
    for (let j = 0; j < m.cols; j++) row.push(texOf(m.get(i, j)));
    lines.push(row.join(' & '));
  }
  const env = settings.matStr ?? (settings.mode === 'inline' ? 'smallmatrix' : m.cols <= 10 ? 'matrix' : 'array');
  const spec = env === 'array' ? `{${'c'.repeat(m.cols)}}` : '';
  const out = `\\begin{${env}}${spec}${lines.join('\\\\')}\\end{${env}}`;
  if (settings.matDelim === '') return out;
  return `\\left${settings.matDelim}${out}\\right${settings.matDelim === '(' ? ')' : ']'}`;
}

/** The order of default_sort_key for the items of a set or the keys of a dict (expressions first, in SymPy's order). */
function sortedItems(items: readonly LatexPrintable[]): LatexPrintable[] {
  const exprs = items.filter((x): x is Expr => x instanceof Expr).sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
  return [...exprs, ...items.filter((x) => !(x instanceof Expr))];
}

/** SymPy `Printer._print` of the LaTeX printer for any printable value. */
function printValue(v: LatexPrintable): string {
  if (v instanceof Expr) return texOf(v);
  if (typeof v === 'number' || typeof v === 'bigint') return texOf(sympify(v));
  if (typeof v === 'boolean') return v ? '\\text{True}' : '\\text{False}';
  // SymPy emptyPrinter: str() in monospace
  if (typeof v === 'string') return `\\mathtt{\\text{${latexEscape(v)}}}`;
  if (v === null) return '\\text{None}';
  const sep = settings.comma ? ';' : ',';
  if (Array.isArray(v)) return `\\left[ ${v.map(printValue).join(`${sep} \\  `)}\\right]`;
  if (v instanceof Map) {
    const keys = sortedItems([...v.keys()]);
    // SymPy separates the items of a dict by commas whatever the decimal separator
    return `\\left\\{ ${keys.map((k) => `${printValue(k)} : ${printValue(v.get(k) ?? null)}`).join(', \\  ')}\\right\\}`;
  }
  if (v instanceof Set) return `\\left\\{${sortedItems([...v]).map(printValue).join(`${sep} `)}\\right\\}`;
  if (isMatrixLike(v)) return printMatrix(v);
  throw new TypeError(`latex: cannot print ${Object.prototype.toString.call(v)}`);
}

/**
 * SymPy `latex(expr, **settings)`: the LaTeX form of an expression, a
 * matrix, or a list, dict, set, string, boolean or null, with the printer's
 * settings ({@link LatexOptions}). Numbers are sympified; a string prints
 * as text, as in SymPy (it is not parsed).
 *
 * A call made while printing (by a node's own LaTeX method) without
 * options uses the settings of the print in progress.
 */
export function latex(expr: LatexPrintable, options?: LatexOptions): string {
  if (depth > 0 && options === undefined) return printValue(expr);
  const prev = settings;
  settings = options === undefined ? DEFAULT_SETTINGS : resolveSettings(options);
  depth++;
  try {
    const tex = printValue(expr);
    const mode = settings.mode;
    if (mode === 'plain') return tex;
    if (mode === 'inline') return `$${tex}$`;
    return settings.itex ? `$$${tex}$$` : `\\begin{${mode}}${tex}\\end{${mode}}`;
  } finally {
    depth--;
    settings = prev;
  }
}

impl.latex = (e: Expr): string => latex(e);

export { isNum };
