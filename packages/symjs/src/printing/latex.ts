// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file LaTeX printer compatible with SymPy's `LatexPrinter` (default settings).
 */

import { isNegative } from '../core/assumptions';
import type { Expr } from '../core/nodes';
import { Add, ExtensionExpr, BoolAtom, Constant, Derivative, Float, Fn, Integral, Limit, Mul, Order, Piecewise, Pow, Rational, Rel, Special, Sym, UndefFn, impl, isNum } from '../core/nodes';
import { mul, pow, splitCoeff } from '../core/ops';
import { numNeg } from '../core/num';
import { asOrderedFactors, asOrderedTerms, compareKeys, sortKey } from './sortkey';
import { PREC, declaredPrecedence, floatString, precedence as strPrecedence, startsNegative, str } from './str';
import { BoolOp } from '../core/boolalg';
import { Concrete } from '../core/concrete';
import { DOTS, rangePrintForm, setArgsOrdered, setClass } from './sets';
import { hasSymbolicBounds, isSequence, sequencePrintset } from './sequences';
import { at } from '../core/guard';

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
  const [name, supers, subs] = splitSuperSub(text);
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
  const s = latex(e);
  return precedence(e) <= level ? addParens(s) : s;
}

function needsMulBrackets(e: Expr, first: boolean): boolean {
  if (e instanceof Mul) return !first && startsNegative(e);
  return precedence(e) < PREC.MUL;
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

/** SymPy `parenthesize_super` with the default parenthesize_super=True. */
const parenthesizeSuper = (s: string) => (s.includes('^') ? addParens(s) : s);

/** SymPy `_do_exponent`. */
const doExponent = (tex: string, exp?: string): string => (exp !== undefined ? `\\left(${tex}\\right)^{${exp}}` : tex);
/** `tex^{exp}` when raised to a power. */
const withExponent = (tex: string, exp?: string): string => (exp !== undefined ? `${tex}^{${exp}}` : tex);
/** `head^{exp}` followed by the arguments in parentheses (SymPy _hprint_one_arg_func and the like). */
const headArgs = (head: string, args: readonly Expr[], exp?: string): string => `${withExponent(head, exp)}\\left(${args.map(latex).join(', ')}\\right)`;
/** SymPy `__print_number_polynomial`: B_{n}, or B_{n}\left(x\right) for the polynomial. */
function numberPolynomial(letter: string, args: readonly Expr[], exp?: string): string {
  const head = withExponent(`${letter}_{${latex(at(args, 0))}}`, exp);
  return args.length === 2 ? `${head}\\left(${latex(at(args, 1))}\\right)` : head;
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
const hprintVec = (v: readonly Expr[]): string => v.map(latex).join(', ');

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
  const l = args.map(latex);
  const [a, b, c] = [l[0] ?? '', l[1] ?? '', l[2] ?? ''];
  switch (name) {
    case 'SingularityFunction': {
      const shift = latex(impl.add(at(args, 0), impl.mul(-1, at(args, 1))));
      const power = latex(at(args, 2));
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
      return `\\operatorname{${name === 'betainc' ? 'B' : 'I'}}_{(${c}, ${latex(at(args, 3))})}${sup}\\left(${a}, ${b}\\right)`;
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
  const tex = `{G_{${e.an.length + e.aother.length}, ${e.bm.length + e.bother.length}}^{${e.bm.length}, ${e.an.length}}\\left(\\begin{matrix} ${hprintVec(e.an)} & ${hprintVec(e.aother)} \\\\${hprintVec(e.bm)} & ${hprintVec(e.bother)} \\end{matrix} \\middle| {${latex(e.argument)}} \\right)}`;
  return exp !== undefined ? `{${tex}}^{${exp}}` : tex;
}

/** SymPy `_print_SeqFormula` (and SeqPer, SeqAdd, SeqMul). */
function printSequence(e: ExtensionExpr & Parameters<typeof sequencePrintset>[0]): string {
  if (hasSymbolicBounds(e)) {
    // only a SeqFormula has a formula to print (SymPy fails for the others)
    if (e.name !== 'SeqFormula') return e.printLatex(latex);
    return `\\left\\{${latex(at(e.args, 3))}\\right\\}_{${latex(at(e.args, 0))}=${latex(e.start)}}^{${latex(e.stop)}}`;
  }
  return `\\left[${sequencePrintset(e).map((t) => (t === DOTS ? '\\ldots' : latex(t))).join(', ')}\\right]`;
}

/** Print a function, optionally raised to a power (SymPy prints sin(x)**2 as \sin^{2}...). */
function printFunction(e: Fn, exp?: string): string {
  const args = e.args;
  const x0 = at(args, 0);
  const a = latex(x0);
  const head = ONE_ARG_HEADS[e.name];
  if (head !== undefined) return headArgs(head, args, exp);
  const letter = NUMBER_POLYNOMIALS[e.name];
  if (letter !== undefined) return numberPolynomial(letter, args, exp);
  const parenHead = PAREN_POWER_HEADS[e.name];
  if (parenHead !== undefined) return doExponent(`${parenHead}\\left(${a}\\right)`, exp);
  const bessel = BESSEL_SYMBOLS[e.name];
  if (bessel !== undefined) {
    // SymPy _hprint_BesselBase: J^{exp}_{\nu}\left(z\right)
    return `${withExponent(bessel, exp)}_{${a}}\\left(${latex(at(args, 1))}\\right)`;
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
    case 'im':
      // SymPy _print_re / _print_im: the argument parenthesized at atom level
      return doExponent(`\\operatorname{${e.name}}{${parenthesize(x0, PREC.ATOM)}}`, exp);
    case 'log':
      return withExponent(`\\log{\\left(${a} \\right)}`, exp);
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
      return withExponent(`{\\binom{${a}}{${latex(at(args, 1))}}}`, exp);
    case 'beta':
      return headArgs('\\operatorname{B}', args.length === 1 ? [x0, x0] : args, exp);
    case 'expint':
      return `\\operatorname{E}_{${a}}${withExponent('', exp)}\\left(${latex(at(args, 1))}\\right)`;
    case 'ff':
      return doExponent(`{\\left(${a}\\right)}_{${parenthesize(at(args, 1), PREC.FUNC)}}`, exp);
    case 'rf':
      return doExponent(`{${parenthesize(x0, PREC.FUNC)}}^{\\left(${latex(at(args, 1))}\\right)}`, exp);
    case 'LambertW': {
      const k = args[1];
      return `W${withExponent('', exp)}${k ? `_{${latex(k)}}` : ''}\\left(${a}\\right)`;
    }
    case 'euler': {
      const tex = withExponent(`E_{${a}}`, exp);
      const z = args[1];
      return z ? `${tex}\\left(${latex(z)}\\right)` : tex;
    }
    case 'divisor_sigma': {
      const k = args[1];
      return `\\sigma${withExponent('', exp)}${k ? `_${latex(k)}` : ''}\\left(${a}\\right)`;
    }
    case 'KroneckerDelta': {
      const b = at(args, 1);
      const atomic = (v: Expr) => v instanceof Sym || isNum(v) || v instanceof Constant || v instanceof Special;
      const tex = atomic(x0) && atomic(b) ? `\\delta_{${a} ${latex(b)}}` : `\\delta_{${a}, ${latex(b)}}`;
      return doExponent(tex, exp);
    }
    case 'Min':
    case 'Max': {
      // SymPy _hprint_variadic_function: the arguments in default_sort_key order
      const sorted = [...args].sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
      return withExponent(`\\${e.name.toLowerCase()}\\left(${sorted.map(latex).join(', ')}\\right)`, exp);
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
      const params = args.slice(1, -1).map(latex);
      const sup = params.length ? `^{\\left(${params.join(',')}\\right)}` : '';
      const tex = `${letter}_{${a}}${sup}\\left(${latex(at(args, args.length - 1))}\\right)`;
      return exp !== undefined ? `\\left(${tex}\\right)^{${exp}}` : tex;
    }
    case 'hankel1':
    case 'hankel2':
    case 'hn1':
    case 'hn2': {
      // SymPy _hprint_BesselBase with a symbol that has a superscript: the power wraps the call
      const tex = `${e.name.startsWith('hankel') ? 'H' : 'h'}^{(${e.name.slice(-1)})}_{${a}}\\left(${latex(at(args, 1))}\\right)`;
      return exp !== undefined ? `\\left(${tex}\\right)^{${exp}}` : tex;
    }
    case 'Ynm':
    case 'Znm': {
      const tex = `${e.name.charAt(0)}_{${a}}^{${latex(at(args, 1))}}\\left(${latex(at(args, 2))},${latex(at(args, 3))}\\right)`;
      return exp !== undefined ? `\\left(${tex}\\right)^{${exp}}` : tex;
    }
    case 'mathieuc':
    case 'mathieus':
    case 'mathieucprime':
    case 'mathieusprime': {
      // SymPy __print_mathieu_functions: the exponent follows the arguments
      const sup = e.name.endsWith('prime') ? '^{\\prime}' : '';
      return `${e.name.charAt(7).toUpperCase()}${sup}\\left(${args.map(latex).join(', ')}\\right)${exp !== undefined ? `^{${exp}}` : ''}`;
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
    default: {
      // SymPy _print_Function for functions without their own printer
      const name = exp !== undefined ? `${parenthesizeSuper(hprintFunction(e.name))}^{${exp}}` : hprintFunction(e.name);
      return `${name}{\\left(${args.map(latex).join(',')} \\right)}`;
    }
  }
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
    let t = latex(term);
    if (needsMulBrackets(term, i === 0)) t = addParens(t);
    if (BETWEEN_NUMBERS[0].test(last) && BETWEEN_NUMBERS[1].test(str(term))) tex += ' \\cdot ';
    else if (tex) tex += ' ';
    tex += t;
    last = t;
  });
  return tex;
}

function convertFactors(fs: Expr[]): string {
  if (fs.length === 0) return '1';
  if (fs.length === 1) return latex(at(fs, 0));
  return convertArgs(asOrderedFactors(new Mul(fs)));
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
    tex += expr instanceof Mul ? convertArgs(asOrderedFactors(expr)) : latex(expr);
  } else {
    tex += `\\frac{${convertFactors(numer)}}{${convertFactors(denom)}}`;
  }
  if (includeParens) tex += ')';
  return tex;
}

function printPow(e: Pow): string {
  const [b, x] = e.args;
  if (isExp(e)) return `e^{${latex(x)}}`;
  if (x instanceof Rational) {
    const p = x.p < 0n ? -x.p : x.p;
    if (p === 1n && x.q !== 1n) {
      const base = latex(b);
      const tex = x.q === 2n ? `\\sqrt{${base}}` : `\\sqrt[${x.q}]{${base}}`;
      return x.p < 0n ? `\\frac{1}{${tex}}` : tex;
    }
    if (x.p < 0n && b.isCommutative) return printMulLike(e);
  }
  if (b instanceof Fn) return printFunction(b, latex(x));
  if (b instanceof ExtensionExpr) {
    const named = printNamedFunction(b.name, b.args, latex(x));
    if (named !== undefined) return named;
    if (isMeijer(b)) return printMeijer(b, latex(x));
    // SymPy _print_hyper: the braced form raised to the power
    if (b.name === 'hyper') return `{${latex(b)}}^{${latex(x)}}`;
  }
  if (b instanceof UndefFn) return `${parenthesizeSuper(hprintFunction(b.name))}^{${latex(x)}}{\\left(${b.args.map(latex).join(',')} \\right)}`;
  let base = parenthesize(b, PREC.POW);
  if (b instanceof Sym) base = parenthesizeSuper(base);
  else if (b instanceof Float) base = `{${base}}`;
  return `${base}^{${latex(x)}}`;
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
    const t = latex(term);
    tex += term instanceof Add ? addParens(t) : t;
  });
  return tex;
}

function floatLatex(f: Float): string {
  const s = floatString(f, true);
  const k = s.indexOf('e');
  if (k < 0) return s;
  const exp = s.slice(k + 1);
  return `${s.slice(0, k)} \\cdot 10^{${exp.startsWith('+') ? exp.slice(1) : exp}}`;
}

export function latex(e: Expr): string {
  if (e instanceof ExtensionExpr) {
    const named = printNamedFunction(e.name, e.args);
    if (named !== undefined) return named;
    if (isMeijer(e)) return printMeijer(e);
    if (isSequence(e)) return printSequence(e);
    if (e.name === 'EmptySequence') return '\\text{EmptySequence}';
  }
  if (e instanceof ExtensionExpr || e instanceof BoolOp) return e.printLatex(latex);
  if (e instanceof Rational) {
    if (e.q === 1n) return `${e.p}`;
    return e.p < 0n ? `- \\frac{${-e.p}}{${e.q}}` : `\\frac{${e.p}}{${e.q}}`;
  }
  if (e instanceof Float) return floatLatex(e);
  if (e instanceof Sym) return symbolLatex(e.name);
  if (e instanceof Constant) {
    return { pi: '\\pi', E: 'e', I: 'i', EulerGamma: '\\gamma', Catalan: 'G', GoldenRatio: '\\phi', TribonacciConstant: '\\text{TribonacciConstant}' }[e.name];
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
    const op = { Eq: '=', Ne: '\\neq', Lt: '<', Le: '\\leq', Gt: '>', Ge: '\\geq' }[e.op];
    return `${latex(e.lhs)} ${op} ${latex(e.rhs)}`;
  }
  if (e instanceof Piecewise) {
    const pairs = e.pairs;
    const parts = pairs.map(([x, c], i) =>
      i === pairs.length - 1 && c instanceof BoolAtom && c.value
        ? `${latex(x)} & \\text{otherwise}`
        : `${latex(x)} & \\text{for}\\: ${latex(c)}`,
    );
    return `\\begin{cases} ${parts.join(' \\\\')} \\end{cases}`;
  }
  if (e instanceof UndefFn) return `${hprintFunction(e.name)}{\\left(${e.args.map(latex).join(',')} \\right)}`;
  if (e instanceof Derivative) {
    const partial = impl.freeSymbols(e.expr).size > 1;
    const d = partial ? '\\partial' : 'd';
    let tex = '';
    let dim = 0;
    for (const [v, n] of [...e.variableCount].reverse()) {
      dim += n;
      tex += n === 1 ? `${d} ${latex(v)}` : `${d} ${parenthesizeSuper(latex(v))}^{${n}}`;
    }
    const head = dim === 1 ? `\\frac{${d}}{${tex}}` : `\\frac{${d}^{${dim}}}{${tex}}`;
    const body = precedence(e.expr) < PREC.MUL ? addParens(latex(e.expr)) : latex(e.expr);
    return `${head} ${body}`;
  }
  if (e instanceof Limit) {
    // SymPy _print_Limit: no direction at an infinite point, a sum or product body in parentheses without a space
    const f = e.expr;
    const p = e.point;
    const d = e.dir === '+-' || (p instanceof Special && (p.name === 'oo' || p.name === '-oo')) ? '' : `^${e.dir}`;
    const head = `\\lim_{${latex(e.variable)} \\to ${latex(p)}${d}}`;
    return f instanceof Add || f instanceof Mul ? `${head}${addParens(latex(f))}` : `${head} ${latex(f)}`;
  }
  if (e instanceof Order) {
    const v = e.variable;
    const p = e.point;
    if (!v || !p || (p instanceof Rational && p.isZero)) return `O\\left(${latex(e.expr)}\\right)`;
    return `O\\left(${latex(e.expr)}; ${latex(v)}\\rightarrow ${latex(p)}\\right)`;
  }
  if (e instanceof Concrete) {
    // SymPy _print_Sum / _print_Product
    const op = e.kind2 === 'Sum' ? '\\sum' : '\\prod';
    const lims = e.limits;
    const one = lims.length === 1 ? lims[0] : undefined;
    const head =
      one
        ? `${op}_{${latex(one[0])}=${latex(one[1])}}^{${latex(one[2])}} `
        : `${op}_{\\substack{${lims.map(([k, a, b]) => `${latex(a)} \\leq ${latex(k)} \\leq ${latex(b)}`).join('\\\\')}}} `;
    return head + (e.function instanceof Add ? addParens(latex(e.function)) : latex(e.function));
  }
  if (e instanceof Integral) {
    // nested integrals: outer signs first, differentials innermost first
    const heads: string[] = [];
    const ds: string[] = [];
    let cur: Expr = e;
    while (cur instanceof Integral) {
      const lim = cur.limits;
      heads.push(lim ? `\\int\\limits_{${latex(lim[0])}}^{${latex(lim[1])}}` : '\\int');
      ds.unshift(`\\, d${latex(cur.variable)}`);
      cur = cur.integrand;
    }
    const body = precedence(cur) < PREC.MUL ? addParens(latex(cur)) : latex(cur);
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
    return args.map((a) => (SET_OPERATORS[String(setClass(a))] !== undefined ? addParens(latex(a)) : latex(a))).join(op);
  }
  switch (cls) {
    case 'Interval': {
      const [a, b, lo, ro] = [at(e.args, 0), at(e.args, 1), at(e.args, 2), at(e.args, 3)];
      if (a.key === b.key) return `\\left\\{${latex(a)}\\right\\}`;
      const open = (x: Expr) => x instanceof BoolAtom && x.value;
      return `\\left${open(lo) ? '(' : '['}${latex(a)}, ${latex(b)}\\right${open(ro) ? ')' : ']'}`;
    }
    case 'Range': {
      const shown = rangePrintForm(e, 3);
      // SymPy _print_symbolic_range: a Range whose elements are unknown
      if ('symbolic' in shown) return `\\text{Range}\\left(${shown.symbolic.map(latex).join(', ')}\\right)`;
      return `\\left\\{${shown.elements.map((t) => (t === DOTS ? '\\ldots' : latex(t))).join(', ')}\\right\\}`;
    }
    case 'FiniteSet':
      return `\\left\\{${[...e.args].sort((u, v) => compareKeys(sortKey(u), sortKey(v))).map(latex).join(', ')}\\right\\}`;
    case 'ImageSet': {
      const [v, expr, base] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
      return `\\left\\{${latex(expr)}\\; \\middle|\\; ${latex(v)} \\in ${latex(base)}\\right\\}`;
    }
    case 'ConditionSet': {
      const [v, cond, base] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
      if (setClass(base) === 'UniversalSet') return `\\left\\{${latex(v)}\\; \\middle|\\; ${latex(cond)} \\right\\}`;
      return `\\left\\{${latex(v)}\\; \\middle|\\; ${latex(v)} \\in ${latex(base)} \\wedge ${latex(cond)} \\right\\}`;
    }
    default:
      // the other sets print themselves (ProductSet, PowerSet, ComplexRegion, ...)
      return 'printLatex' in e && typeof e.printLatex === 'function' ? String(e.printLatex(latex)) : e.key;
  }
}

impl.latex = latex;

export { isNum };
