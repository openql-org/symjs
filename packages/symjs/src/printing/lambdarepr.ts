// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Based on SymPy's printing/lambdarepr.py and printing/pycode.py.

import { Add, Constant, Float, Fn, Mul, Pow, Rational, S, Special, Sym, type Expr, type ExprLike } from '../core/nodes';
import { mul, splitCoeff, sympify } from '../core/ops';
import { NotImplementedError } from '../core/errors';
import { asOrderedFactors, asOrderedTerms } from './sortkey';
import { PRECEDENCE, precedence, str } from './str';

const functions: Readonly<Record<string, string>> = {
  abs: 'abs', acos: 'mpmath.acos', asin: 'mpmath.asin', atan: 'mpmath.atan',
  cos: 'mpmath.cos', cosh: 'mpmath.cosh', exp: 'mpmath.exp', log: 'mpmath.log',
  sin: 'mpmath.sin', sinh: 'mpmath.sinh', tan: 'mpmath.tan', tanh: 'mpmath.tanh',
};
const constants: Readonly<Record<string, string>> = {
  E: 'mpmath.e', pi: 'mpmath.pi', I: '1j',
  GoldenRatio: 'mpmath.phi', EulerGamma: 'mpmath.euler', Catalan: 'mpmath.catalan',
  oo: 'mpmath.inf', '-oo': '-mpmath.inf', nan: 'mpmath.nan',
};

/**
 * Python expression printer for interval arithmetic with mpmath.
 *
 * @see SymPy `sympy.printing.lambdarepr.IntervalPrinter`
 */
export class IntervalPrinter {
  /**
   * Formats the supplied value using the printer settings.
   *
   * @param expression - The value to format.
   * @returns The formatted text.
   * @see SymPy `sympy.printing.lambdarepr.IntervalPrinter.doprint`
   */
  doprint(expression: ExprLike): string {
    return this.print(sympify(expression));
  }
  private grouped(e: Expr, level: number): string {
    const value = this.print(e);
    return precedence(e) <= level ? `(${value})` : value;
  }
  private print(e: Expr): string {
    if (e instanceof Rational) return `mpi('${str(e)}')`;
    if (e instanceof Float) {
      const { man, exp } = e.mpf;
      const sign = man < 0n ? 1 : 0;
      const magnitude = man < 0n ? -man : man;
      return `mpmath.mpf((${sign}, ${magnitude}, ${exp}, ${magnitude === 0n ? 0 : magnitude.toString(2).length}))`;
    }
    if (e instanceof Sym) return e.name;
    if (e instanceof Pow) {
      if (e.base.equals(S.E)) return `mpmath.exp(${this.print(e.exp)})`;
      return `${this.grouped(e.base, PRECEDENCE.Pow)}**${this.grouped(e.exp, PRECEDENCE.Pow)}`;
    }
    if (e instanceof Add) {
      return asOrderedTerms(e).map((term) => this.print(term)).join(' + ').replace(/ \+ -/g, ' - ');
    }
    if (e instanceof Mul) {
      const [c] = splitCoeff(e);
      const positive = c.isNegative ? mul(-1, e) : e;
      const factors = asOrderedFactors(positive);
      const numerator: Expr[] = [], denominator: Expr[] = [];
      for (const f of factors) {
        if (f instanceof Pow && f.isCommutative && f.exp instanceof Rational && f.exp.isNegative && !f.base.equals(S.E)) {
          denominator.push(f.exp.equals(S.NegOne) ? f.base : new Pow(f.base, mul(-1, f.exp)));
        } else numerator.push(f);
      }
      const printFactors = (xs: Expr[]) => xs.map((x) => this.grouped(x, PRECEDENCE.Mul)).join('*');
      const negative = c.isNegative ? '-' : '';
      const n = numerator.length ? printFactors(numerator) : this.print(S.One);
      if (!denominator.length) return negative + n;
      const d = printFactors(denominator);
      return `${negative}${n}/${denominator.length === 1 ? d : `(${d})`}`;
    }
    if (e instanceof Fn && Object.hasOwn(functions, e.name)) {
      return `${functions[e.name]}(${e.args.map((a) => this.print(a)).join(', ')})`;
    }
    if ((e instanceof Constant || e instanceof Special) && Object.hasOwn(constants, e.name)) return String(constants[e.name]);
    throw new NotImplementedError(`interval printing is unsupported for ${str(e)}`);
  }
}
