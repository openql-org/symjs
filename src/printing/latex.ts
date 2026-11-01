// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file LaTeX printer.
 */

import { Add, Constant, Expr, Float, Fn, Mul, Pow, Rational, Sym, impl, isNum } from '../core/nodes';
import { mul, pow, splitCoeff } from '../core/ops';
import { floatString, isNegativeTerm, printOrder, splitFraction } from './order';
import { PREC, precedence } from './str';

const GREEK = new Set([
  'alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lambda',
  'mu', 'nu', 'xi', 'pi', 'rho', 'sigma', 'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega',
  'Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Upsilon', 'Phi', 'Psi', 'Omega',
]);

function symbolLatex(name: string): string {
  const m = /^([A-Za-z]+)(?:_?(\d+)|_(\w+))?$/.exec(name);
  if (!m) return name.replace(/_/g, '\\_');
  const head = GREEK.has(m[1]!) ? `\\${m[1]}` : m[1]!.length > 1 ? `\\mathrm{${m[1]}}` : m[1]!;
  const sub = m[2] ?? m[3];
  return sub !== undefined ? `${head}_{${sub}}` : head;
}

const FN_LATEX: Record<string, string> = {
  sin: '\\sin',
  cos: '\\cos',
  tan: '\\tan',
  asin: '\\arcsin',
  acos: '\\arccos',
  atan: '\\arctan',
  sinh: '\\sinh',
  cosh: '\\cosh',
  tanh: '\\tanh',
  log: '\\log',
  re: '\\operatorname{re}',
  im: '\\operatorname{im}',
  arg: '\\arg',
};

const wrap = (s: string) => `\\left(${s}\\right)`;

function paren(e: Expr, minPrec: number): string {
  const s = latex(e);
  return precedence(e) < minPrec ? wrap(s) : s;
}

function isNegExp(x: Expr): boolean {
  const [c] = splitCoeff(x);
  return c.isNegative;
}

function joinFactors(parts: { s: string; numeric: boolean }[]): string {
  let out = '';
  parts.forEach((p, i) => {
    if (i > 0) out += parts[i - 1]!.numeric && p.numeric ? ' \\cdot ' : ' ';
    out += p.s;
  });
  return out;
}

export function latex(e: Expr): string {
  if (e instanceof Rational) {
    if (e.q === 1n) return `${e.p}`;
    const s = `\\frac{${e.p < 0n ? -e.p : e.p}}{${e.q}}`;
    return e.p < 0n ? `-${s}` : s;
  }
  if (e instanceof Float) return floatString(e);
  if (e instanceof Sym) return symbolLatex(e.name);
  if (e instanceof Constant) return e.name === 'pi' ? '\\pi' : e.name === 'E' ? 'e' : 'i';
  if (e instanceof Fn) {
    const a = latex(e.args[0]!);
    if (e.name === 'abs') return `\\left|${a}\\right|`;
    if (e.name === 'conjugate') return `\\overline{${a}}`;
    return `${FN_LATEX[e.name] ?? `\\operatorname{${e.name}}`}${wrap(a)}`;
  }
  if (e instanceof Add) {
    const terms = printOrder(e.args);
    let out = latex(terms[0]!);
    for (const t of terms.slice(1)) {
      if (isNegativeTerm(t)) out += ` - ${paren(mul(-1, t), PREC.MUL)}`;
      else out += ` + ${latex(t)}`;
    }
    return out;
  }
  if (e instanceof Mul) {
    const f = splitFraction(e);
    const num: { s: string; numeric: boolean }[] = [];
    const den: { s: string; numeric: boolean }[] = [];
    if (f.coeff instanceof Rational) {
      if (f.coeff.p !== 1n) num.push({ s: `${f.coeff.p}`, numeric: true });
      if (f.coeff.q !== 1n) den.push({ s: `${f.coeff.q}`, numeric: true });
    } else if (f.coeff.value !== 1) {
      num.push({ s: floatString(f.coeff), numeric: true });
    }
    for (const x of f.num) num.push({ s: paren(x, PREC.MUL), numeric: isNum(x) || isNumericPow(x) });
    for (const x of f.den) den.push({ s: paren(x, PREC.MUL), numeric: isNum(x) || isNumericPow(x) });
    const ns = num.length > 0 ? joinFactors(num) : '1';
    const s = den.length > 0 ? `\\frac{${ns}}{${joinFactors(den)}}` : ns;
    return (f.sign ? '- ' : '') + s;
  }
  if (e instanceof Pow) {
    const [b, x] = e.args;
    if (b instanceof Constant && b.name === 'E') return `e^{${latex(x)}}`;
    if (x instanceof Rational && x.p === 1n && x.q === 2n) return `\\sqrt{${latex(b)}}`;
    if (x instanceof Rational && x.p === 1n) return `\\sqrt[${x.q}]{${latex(b)}}`;
    if (isNegExp(x)) return `\\frac{1}{${latex(pow(b, mul(-1, x)))}}`;
    if (b instanceof Fn && FN_LATEX[b.name] && x instanceof Rational && x.isInteger) {
      return `${FN_LATEX[b.name]}^{${x.p}}${wrap(latex(b.args[0]!))}`;
    }
    const bs = precedence(b) < PREC.ATOM || isNum(b) ? paren(b, PREC.ATOM) : latex(b);
    return `${bs}^{${latex(x)}}`;
  }
  return e.key;
}

const isNumericPow = (e: Expr) => e instanceof Pow && isNum(e.base);

impl.latex = latex;
