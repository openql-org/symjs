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
import { asOrderedFactors, asOrderedTerms } from './sortkey';
import { PREC, floatString, precedence, startsNegative, str } from './str';

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
    else if (part.startsWith('_')) subs.push(part.slice(1));
  }
  name ??= '';
  const m = /^([^\W\d_]+)(\d+)$/u.exec(name);
  if (m) {
    name = m[1]!;
    subs.unshift(m[2]!);
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

function hprintFunction(name: string): string {
  if (ACCEPTED_FUNCTIONS.has(name)) return `\\${name}`;
  if (name.length === 1 || name.startsWith('\\')) return name;
  return `\\operatorname{${name}}`;
}

const parenthesizeSuper = (s: string) => (s.includes('^') ? `{${s}}` : s);

/** Print a function, optionally raised to a power (SymPy prints sin(x)**2 as \sin^{2}...). */
function printFunction(e: Fn, exp?: string): string {
  const a = latex(e.args[0]!);
  switch (e.name) {
    case 'abs': {
      const tex = `\\left|{${a}}\\right|`;
      return exp !== undefined ? `${tex}^{${exp}}` : tex;
    }
    case 'adjoint': {
      const base = `${parenthesize(e.args[0]!, PREC.POW)}^{\\dagger}`;
      return exp !== undefined ? `\\left(${base}\\right)^{${exp}}` : base;
    }
    case 'conjugate': {
      const tex = `\\overline{${a}}`;
      return exp !== undefined ? `${tex}^{${exp}}` : tex;
    }
    case 're':
    case 'im': {
      const tex = `\\operatorname{${e.name}}{\\left(${parenthesize(e.args[0]!, PREC.ATOM)}\\right)}`;
      return exp !== undefined ? `${tex}^{${exp}}` : tex;
    }
    case 'besselj':
    case 'bessely':
    case 'besseli':
    case 'besselk': {
      // SymPy: J_{\nu}\left(z\right)
      const sym = { besselj: 'J', bessely: 'Y', besseli: 'I', besselk: 'K' }[e.name];
      const tex = `${sym}_{${latex(e.args[0]!)}}\\left(${latex(e.args[1]!)}\\right)`;
      return exp !== undefined ? `${sym}_{${latex(e.args[0]!)}}^{${exp}}\\left(${latex(e.args[1]!)}\\right)` : tex;
    }
    case 'airyai':
    case 'airybi':
    case 'airyaiprime':
    case 'airybiprime': {
      const base = e.name.startsWith('airyai') ? 'Ai' : 'Bi';
      const prime = e.name.endsWith('prime') ? '^\\prime' : '';
      const tex = `${base}${prime}\\left(${a}\\right)`;
      return exp !== undefined ? `${base}${prime}^{${exp}}\\left(${a}\\right)` : tex;
    }
    default: {
      const name = exp !== undefined ? `${parenthesizeSuper(hprintFunction(e.name))}^{${exp}}` : hprintFunction(e.name);
      return `${name}{\\left(${a} \\right)}`;
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
  if (fs.length === 1) return latex(fs[0]!);
  return convertArgs(asOrderedFactors(new Mul(fs)));
}

function printMulLike(e: Expr): string {
  let expr = e;
  let tex = '';
  let includeParens = false;
  if (startsNegative(expr)) {
    const [c, rest] = splitCoeff(expr);
    const pc = numNeg(c);
    expr = pc instanceof Rational && pc.isOne ? rest : new Mul([pc, ...(rest instanceof Mul ? rest.args : [rest])]);
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
  if (e instanceof ExtensionExpr) return e.printLatex(latex);
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
    const [f, z, z0] = e.args;
    const d = e.dir === '+-' ? '' : `^${e.dir}`;
    const body = precedence(f!) < PREC.ADD ? addParens(latex(f!)) : latex(f!);
    return `\\lim_{${latex(z!)} \\to ${latex(z0!)}${d}} ${body}`;
  }
  if (e instanceof Order) {
    const [x, v, p] = e.args;
    if (!v || !p || (p instanceof Rational && p.isZero)) return `O\\left(${latex(x!)}\\right)`;
    return `O\\left(${latex(x!)}; ${latex(v)}\\rightarrow ${latex(p)}\\right)`;
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
  return e.key;
}

impl.latex = latex;

export { isNum };
